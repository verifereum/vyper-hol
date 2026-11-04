Theory typedNormalizeContinuation
Ancestors
  fragExec loweringHalt exprLoweringProps stmtLowering emitHelper
  venomExecSemantics compileEnv context venomInst exprLowering
  typedArrayLoopControlMem

Theorem normalize_alloc_continuation_entry[local]:
  compile_alloc_buffer n sa = (buf,sc) /\ cs_extends sc sb /\
  fn_has_code sa sb fn /\ sa.cs_current_insts = [] ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `cs_extends sa sc` by
    (mp_tac (Q.SPECL [`n`, `sa`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `fn_has_code sa sc fn` mp_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  strip_tac >> goal_assum (drule_at Any) >> simp[phi_prefix_length_def, mk_inst_def]
QED

(* Covers every ABI encoder constructor, including dynamic child CFGs. *)
Theorem normalize_abi_return_entry[local]:
  compile_external_return (SOME op) F F info msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ fn_has_code sa sb fn /\ sa.cs_current_insts = [] ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all compile_external_return_abi_parts >> strip_tac >>
  `cs_extends sa' sb'` by
    (mp_tac (cj 2 ci_mono_compile_abi_encode) >>
     disch_then (qspecl_then [`buf.buf_operand`, `op`, `info`, `sa'`] mp_tac) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sb' sb` by
    (mp_tac (Q.SPECL [`RETURN`, `[buf.buf_operand; len]`, `[]`, `sb'`]
      ci_mono_emit_inst) >> asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sa' sb` by metis_tac[cs_extends_trans] >>
  drule_all normalize_alloc_continuation_entry >> simp[]
QED

Theorem normalize_external_return_entry:
  compile_external_return ret prim raw info msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ fn_has_code sa sb fn /\ sa.cs_current_insts = [] ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `ret`
  >- (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_external_return_def, optional_unlock_view, emit_inst_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[phi_prefix_length_def, mk_inst_def]) >>
  Cases_on `raw`
  >- (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_external_return_def, optional_unlock_view, emit_op_def, emit_inst_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[phi_prefix_length_def, mk_inst_def]) >>
  Cases_on `prim`
  >- (drule_all compile_external_return_word_parts >> strip_tac >>
      gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[phi_prefix_length_def, mk_inst_def]) >>
  drule_all normalize_abi_return_entry >> simp[]
QED

(* Zero offsets emit no instruction: use the enclosing continuation certificate. *)
Theorem normalize_field_offset_entry:
  compile_with_byte_offset op off sa = (out,sb) /\
  fn_has_code sa sb fn /\ sa.cs_current_insts = [] /\
  (off = 0 ==> ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `off = 0`
  >- simp[compile_with_byte_offset_def, comp_return_def] >>
  simp[compile_with_byte_offset_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  simp[phi_prefix_length_def, mk_inst_def]
QED

Theorem normalize_array_backedge_entry:
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = ec.cs_current_insts ++ typed_sa_backedge_insts id ctr nv hdr /\
  phi_prefix_length ec.cs_current_insts = 0 ==>
  ?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
    phi_prefix_length entry.bb_instructions = 0
Proof
  strip_tac >> qexists_tac `bb` >> simp[] >>
  Cases_on `ec.cs_current_insts` >>
  gvs[typed_sa_backedge_insts_def, phi_prefix_length_def, mk_inst_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED
