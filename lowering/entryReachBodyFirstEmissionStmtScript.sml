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
