Theory entryReachBodyFirstEmissionStmt
Ancestors
  entryReachBodyFirstEmissionExpr entryReachBodyFirstEmissionSupport
  compilerFirstEmission externalEntryShape stmtLowering exprLowering
  compileEnv fragExec emitHelper venomInst list

Theorem first_emission_log_eval_all[local]:
  !ce es a x b. compile_log_eval_all ce es a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> Induct >>
  pure_rewrite_tac[compile_log_eval_all_def, LET_THM] >> BETA_TAC
  >- metis_tac[first_emission_return] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >>
      metis_tac[first_emission_compile_expr]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_log_topic[local]:
  !v bs a x b. compile_encode_log_topic v bs a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `bs` >>
  pure_rewrite_tac[contextTheory.compile_encode_log_topic_def] >>
  simp[comp_return_def, cs_extends_refl] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac >>
  (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[])
QED

Theorem first_emission_log_topic_ops[local]:
  !ops a x b. compile_log_topic_ops ops a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >> pure_rewrite_tac[compile_log_topic_ops_def]
  >- metis_tac[first_emission_return] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_log_topic] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  metis_tac[first_emission_return]
QED

Theorem first_emission_log_store_data[local]:
  !ce ops dst off a x b. compile_log_store_data ce ops dst off a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `ops` >>
  pure_rewrite_tac[compile_log_store_data_def, LET_THM] >> BETA_TAC
  >- metis_tac[first_emission_return] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  irule cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_emit_helpers] >>
      IF_CASES_TAC >> simp[cs_appends_emit_helpers] >>
      rw[cs_appends_def] >> metis_tac[compile_store_bytestring_labels, pairTheory.SND]) >>
  rw[cs_appends_def] >> metis_tac[stmt_list_helpers_labels, pairTheory.SND]
QED

Theorem first_emission_imm_store_word[local]:
  !imm off v a x b. compile_imm_store_word imm off v a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> Cases_on `imm` >> pure_rewrite_tac[contextTheory.compile_imm_store_word_def,
    optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[]) >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers]
QED

Theorem first_emission_store_at_loc[local]:
  !imm dst v loc a x b. compile_store_at_loc imm dst v loc a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `loc`
  >- (rewrite_tac[compile_store_at_loc_def] >> rpt strip_tac >>
      drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  rename1 `SOME l` >> Cases_on `l` >> rewrite_tac[compile_store_at_loc_def]
  >~ [`compile_imm_store_word _ _ _ _ = _`] >- metis_tac[first_emission_imm_store_word] >>
  rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED

Theorem first_emission_revert_with_reason[local]:
  !ce msg ty sz a x b. compile_revert_with_reason ce msg ty sz a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >>
  `!n. cs_appends (compile_alloc_buffer n)` by
    (rw[cs_appends_def] >> metis_tac[compile_alloc_buffer_labels, pairTheory.SND]) >>
  `!vv. cs_appends (unwrap_value ce vv)` by
    (rw[cs_appends_def] >> metis_tac[unwrap_value_labels, pairTheory.SND]) >>
  pure_rewrite_tac[compile_revert_with_reason_def, LET_THM] >> BETA_TAC >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> BETA_TAC >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac,
              gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_return])
QED

Theorem first_emission_reason_message[local]:
  !ce e a x b. compile_reason_message ce e a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `e`
  >~ [`compile_reason_message ce (Literal ty lit)`] >-
  (Cases_on `ty`
   >~ [`BaseT bt`] >-
   (Cases_on `bt`
    >~ [`StringT n`] >-
    (Cases_on `lit`
     >~ [`StringL s`] >-
     (pure_rewrite_tac[compile_reason_message_def] >>
  pure_rewrite_tac[compile_bytelike_literal_def, LET_THM] >> BETA_TAC >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[first_emission_alloc_buffer] >>
      gen_tac >> simp[LET_THM, GSYM cs_appends_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers] >>
      irule cs_appends_ignore_bind >> simp[cs_appends_return] >>
      rw[cs_appends_def] >> metis_tac[compile_store_byte_chunks_labels, pairTheory.SND]) >>
  metis_tac[first_emission_return]) >>
     rewrite_tac[compile_reason_message_def] >> metis_tac[first_emission_compile_expr]) >>
    rewrite_tac[compile_reason_message_def] >> metis_tac[first_emission_compile_expr]) >>
   rewrite_tac[compile_reason_message_def] >> metis_tac[first_emission_compile_expr]) >>
  rewrite_tac[compile_reason_message_def] >> metis_tac[first_emission_compile_expr]
QED

Theorem first_emission_nonreentrant_unlock[local]:
  !nk ut iv a x b. compile_nonreentrant_unlock nk ut iv a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> pure_rewrite_tac[contextTheory.compile_nonreentrant_unlock_def] >>
  IF_CASES_TAC >- metis_tac[first_emission_return] >>
  IF_CASES_TAC >> rpt strip_tac >>
  drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED

Theorem first_emission_external_return[local]:
  !rv pw raw ei sz nr nk ut iv a x b.
  compile_external_return rv pw raw ei sz nr nk ut iv a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_external_return_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[first_emission_nonreentrant_unlock, first_emission_return]) >>
  Cases_on `rv` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      irule cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  IF_CASES_TAC >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer]
  >- (gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      irule cs_appends_bind >> simp[cs_appends_return] >> gen_tac >>
      irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers])
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  irule cs_appends_bind >> simp[cs_appends_return] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >>
  rw[cs_appends_def] >> metis_tac[compile_abi_encode_labels, pairTheory.SND]
QED

Theorem first_emission_copy_memory[local]:
  !dst src n a x b. compile_copy_memory dst src n a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `n` >> pure_rewrite_tac[contextTheory.compile_copy_memory_def]
  >- metis_tac[first_emission_return] >>
  rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED

Theorem first_emission_store_bytestring[local]:
  !src dst a x b. compile_store_bytestring src dst a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> pure_rewrite_tac[contextTheory.compile_store_bytestring_def,
    contextTheory.compile_bytestring_copy_len_def, LET_THM] >> BETA_TAC >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
      irule cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers]
QED

Theorem first_emission_byte_offset[local]:
  !op off a x b. compile_with_byte_offset op off a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> pure_rewrite_tac[contextTheory.compile_with_byte_offset_def] >>
  IF_CASES_TAC >- metis_tac[first_emission_return] >>
  rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED
