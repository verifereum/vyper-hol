Theory entryReachBodyFirstEmissionStmt
Ancestors
  entryReachBodyFirstEmissionExpr entryReachBodyFirstEmissionSupport
  entryReachBodyFirstEmissionExprSupport
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

Theorem first_emission_typed_memory_family[local]:
  (!ce dst dt src st a x b. compile_store_memory_typed ce dst dt src st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst src dts sts doff soff a x b. compile_typed_copy_fields ce dst src dts sts doff soff a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst dt src st n a x b. compile_copy_sarray_typed ce dst dt src st n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst dt cap src st a x b. compile_copy_dynarray_typed ce dst dt cap src st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst src dfs sfs doff soff a x b. compile_struct_typed_copy ce dst src dfs sfs doff soff a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac contextTheory.compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >> metis_tac[first_emission_return])
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >> metis_tac[first_emission_return])
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >> metis_tac[first_emission_return])
  >> suspend "struct"
QED

Resume first_emission_typed_memory_family[fields]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> metis_tac[]
QED

Resume first_emission_typed_memory_family[struct]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name`
  >~ [`ALOOKUP sfs name = SOME p`] >-
  (PairCases_on `p` >>
   rule_assum_tac (PURE_REWRITE_RULE [optionTheory.option_case_def, pairTheory.pair_case_def]) >>
   rule_assum_tac BETA_RULE >>
   rule_assum_tac (PURE_REWRITE_RULE [pairTheory.pair_case_def]) >>
   pure_rewrite_tac[optionTheory.option_case_def, pairTheory.pair_case_def, LET_THM] >> BETA_TAC >>
   pure_rewrite_tac[pairTheory.pair_case_def, pairTheory.FST, pairTheory.SND] >>
   CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
   ho_match_mp_tac first_emission_bind >> conj_tac
   >- metis_tac[first_emission_byte_offset] >>
   gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
   >- metis_tac[first_emission_byte_offset] >>
   gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> metis_tac[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [optionTheory.option_case_def]) >>
  pure_rewrite_tac[optionTheory.option_case_def, LET_THM] >> BETA_TAC >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> metis_tac[]
QED

Resume first_emission_typed_memory_family[sarray]:
  rpt gen_tac >> strip_tac >>
  `!dst dt src st. cs_appends (compile_store_memory_typed ce dst dt src st)` by
    (rw[cs_appends_def] >> metis_tac[cj 1 typed_memory_family_labels, pairTheory.SND]) >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >- metis_tac[first_emission_copy_memory] >>
  ntac 3 (ho_match_mp_tac first_emission_bind >> conj_tac
       >- (rpt strip_tac >> drule (cj 1 first_emission_counters) >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_fresh] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

Resume first_emission_typed_memory_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  `!dst dt src st. cs_appends (compile_store_memory_typed ce dst dt src st)` by
    (rw[cs_appends_def] >> metis_tac[cj 1 typed_memory_family_labels, pairTheory.SND]) >>
  `!dst src len. cs_appends (compile_copy_memory_dynamic dst src len)` by
    simp[contextTheory.compile_copy_memory_dynamic_def, cs_appends_emit_helpers] >>
  once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac,
              IF_CASES_TAC] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

Resume first_emission_typed_memory_family[dispatch]:
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type dt`
  >- (qpat_x_assum `is_word_type dt` mp_tac >> POP_ASSUM_LIST (K all_tac) >> disch_tac >>
      once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      asm_simp_tac bool_ss [] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
      simp[] >> metis_tac[first_emission_store_bytestring]) >>
  reverse (Cases_on `acyclic_struct_metadata ce.ce_struct_fields`)
  >- (once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >> simp[] >>
      rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  Cases_on `dt` >> Cases_on `st`
  >~ [`compile_store_memory_typed ce dst (ArrayT dt db) src (ArrayT st sb)`] >-
  (Cases_on `db` >> Cases_on `sb` >> gvs[] >>
   once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
   simp[LET_THM] >> metis_tac[first_emission_copy_memory]) >>
  gvs[] >> once_rewrite_tac[contextTheory.compile_store_memory_typed_def] >>
  simp[LET_THM] >> metis_tac[first_emission_copy_memory]
QED
Finalise first_emission_typed_memory_family

Theorem first_emission_store_memory[local]:
  !ce src dst dt st a x b. compile_store_memory ce src dst dt st a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> rewrite_tac[contextTheory.compile_store_memory_def] >>
  IF_CASES_TAC
  >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC >- metis_tac[first_emission_store_bytestring] >>
  IF_CASES_TAC >> metis_tac[first_emission_typed_memory_family, first_emission_copy_memory]
QED

Theorem first_emission_load_tuple_elements[local]:
  !ce op tys off a x b. compile_load_tuple_elements ce op tys off a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `tys` >>
  pure_rewrite_tac[compile_load_tuple_elements_def, LET_THM] >> BETA_TAC
  >- metis_tac[first_emission_return] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_return] >>
  rw[cs_appends_def] >> metis_tac[cj 6 stmt_list_helpers_labels, pairTheory.SND]
QED

Theorem first_emission_internal_return[local]:
  !ce rv pc n rt st ts rb a x b. compile_internal_return ce rv pc n rt st ts rb a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_internal_return_def] >>
  IF_CASES_TAC
  >- (Cases_on `rv` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
      IF_CASES_TAC
      >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
      map_every qid_spec_tac [`b`, `x`, `a`] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[first_emission_load_tuple_elements] >>
      rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  Cases_on `rb` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  Cases_on `rv` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[first_emission_store_memory] >>
  rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED

Theorem first_emission_lit_byte_offset[local]:
  !op off a x b. compile_lit_byte_offset op off a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> rewrite_tac[contextTheory.compile_lit_byte_offset_def] >>
  IF_CASES_TAC >- metis_tac[first_emission_return] >>
  Cases_on `op` >> simp_tac (srw_ss()) []
  >~ [`comp_return _ _ = _`] >- metis_tac[first_emission_return] >>
  rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED

Theorem first_emission_imm_store_words[local]:
  !imm src dst n off a x b. compile_imm_store_words imm src dst n off a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `n` >> pure_rewrite_tac[contextTheory.compile_imm_store_words_def]
  >- metis_tac[first_emission_return] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_lit_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  match_mp_tac cs_appends_bind >> conj_tac
  >- (rw[cs_appends_def] >> metis_tac[compile_lit_byte_offset_labels, pairTheory.SND]) >>
  gen_tac >> BETA_TAC >> match_mp_tac cs_appends_ignore_bind >> conj_tac >>
  rw[cs_appends_def] >> metis_tac[compile_imm_store_word_labels, compile_imm_store_words_labels, pairTheory.SND]
QED

Theorem first_emission_word_copy_loop[local]:
  !src dst n ll sl ctor a x b. compile_word_copy_loop src dst n ll sl ctor a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >>
  `!op. cs_appends (compile_ptr_load ctor NONE ll op)` by
    (rw[cs_appends_def] >> metis_tac[compile_ptr_load_labels, pairTheory.SND]) >>
  `!op v. cs_appends (compile_ptr_store ctor NONE sl op v)` by
    (rw[cs_appends_def] >> metis_tac[compile_ptr_store_labels, pairTheory.SND]) >>
  pure_rewrite_tac[contextTheory.compile_word_copy_loop_def, LET_THM] >> BETA_TAC >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ntac 3 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- (rpt strip_tac >> drule (cj 1 first_emission_counters) >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_fresh] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac, IF_CASES_TAC] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

Theorem first_emission_lit_byte_offset[local]:
  !op off a x b. compile_lit_byte_offset op off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> pure_rewrite_tac[contextTheory.compile_lit_byte_offset_def] >>
  IF_CASES_TAC >- metis_tac[first_emission_return] >>
  Cases_on `op` >> pure_rewrite_tac[operand_case_def] >>
  TRY (metis_tac[first_emission_return]) >>
  rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED

Theorem first_emission_store_slots_family[local]:
  (!cenv src slot ty tr a x b. compile_store_slots cenv src slot ty tr a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!cenv src slot ms mo so tr a x b.
    compile_store_slots_members cenv src slot ms mo so tr a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!cenv src slot elem cnt tr a x b.
    compile_copy_elements_to_slots cenv src slot elem cnt tr a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac contextTheory.compile_store_slots_ind >> rpt conj_tac
  >- suspend "slots"
  >- (rpt gen_tac >> once_rewrite_tac[contextTheory.compile_store_slots_def] >>
      metis_tac[first_emission_return])
  >- suspend "members"
  >> suspend "elements"
QED

Resume first_emission_store_slots_family[members]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[contextTheory.compile_store_slots_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_lit_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_lit_byte_offset] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> metis_tac[]
QED

Resume first_emission_store_slots_family[elements]:
  rpt gen_tac >> strip_tac >>
  `!src slot. cs_appends (compile_store_slots cenv src slot elem tr)` by
    (rw[cs_appends_def] >> metis_tac[cj 1 compile_store_slots_labels, pairTheory.SND]) >>
  once_rewrite_tac[contextTheory.compile_store_slots_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ntac 3 (ho_match_mp_tac first_emission_bind >> conj_tac
       >- (rpt strip_tac >> drule (cj 1 first_emission_counters) >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_fresh] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

Resume first_emission_store_slots_family[slots]:
  rpt gen_tac >> strip_tac >>
  `!src slot cnt. cs_appends (compile_word_copy_loop_op src slot cnt LocMemory
                     (if tr then LocTransient else LocStorage) F)` by
    (rw[cs_appends_def] >> metis_tac[compile_word_copy_loop_op_labels, pairTheory.SND]) >>
  `!src slot elem cnt. cs_appends (compile_copy_elements_to_slots cenv src slot elem cnt tr)` by
    (rw[cs_appends_def] >> metis_tac[cj 3 compile_store_slots_labels, pairTheory.SND]) >>
  once_rewrite_tac[contextTheory.compile_store_slots_def] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_strong >>
          ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
          gen_tac >> rewrite_tac[GSYM cs_appends_def] >> simp[cs_appends_emit_helpers]) >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (Cases_on `tr` >>
          rewrite_tac[contextTheory.compile_memory_to_storage_def,
                      contextTheory.compile_memory_to_transient_def] >>
          metis_tac[first_emission_word_copy_loop]) >>
      metis_tac[first_emission_return]) >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (rewrite_tac[contextTheory.compile_bytestring_word_count_def] >>
          ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
          gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
          irule cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      irule cs_appends_ignore_bind >> simp[cs_appends_return]) >>
  IF_CASES_TAC
  >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  Cases_on `ty` >> pure_rewrite_tac[type_case_def] >> BETA_TAC
  >~ [`ArrayT elem bd`]
  >- (Cases_on `bd` >> pure_rewrite_tac[bound_case_def] >> BETA_TAC
      >- (ho_match_mp_tac first_emission_strong >>
          ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
          gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
          rpt (FIRST [irule cs_appends_bind >> conj_tac,
                      irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
               simp[cs_appends_emit_helpers])) >>
      first_x_assum irule >> simp[])
  >~ [`TupleT tys`] >- (first_x_assum irule >> simp[])
  >~ [`StructT nsid`] >- (first_x_assum irule >> simp[]) >>
  rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED
Finalise first_emission_store_slots_family

Theorem first_emission_assign_value[local]:
  !ce dst loc src pw sl dt st di sz a x b.
  compile_assign_value ce dst loc src pw sl dt st di sz a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  pure_rewrite_tac[compile_assign_value_def, LET_THM,
    contextTheory.compile_memory_to_storage_def,
    contextTheory.compile_memory_to_transient_def] >> BETA_TAC >>
  pure_rewrite_tac[data_location_case_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  rpt (FIRST [ho_match_mp_tac first_emission_bind >> conj_tac,
              ho_match_mp_tac first_emission_ignore_bind >> conj_tac,
              IF_CASES_TAC, gen_tac] >> BETA_TAC) >>
  all_tac
  >>~- ([`emit_void _ _ _ = _`],
    rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`emit_inst _ _ _ _ = _`],
    rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`compile_alloc_buffer _ _ = _`], metis_tac[first_emission_alloc_buffer])
  >>~- ([`comp_return _ _ = _`], metis_tac[first_emission_return])
  >>~- ([`compile_copy_memory _ _ _ _ = _`], metis_tac[first_emission_copy_memory])
  >>~- ([`compile_store_memory _ _ _ _ _ _ = _`], metis_tac[first_emission_store_memory])
  >>~- ([`compile_store_memory_typed _ _ _ _ _ _ = _`], metis_tac[first_emission_typed_memory_family])
  >>~- ([`compile_imm_store_word _ _ _ _ = _`], metis_tac[first_emission_imm_store_word])
  >>~- ([`compile_imm_store_words _ _ _ _ _ _ = _`], metis_tac[first_emission_imm_store_words])
  >>~- ([`emit_op _ _ _ = _`],
    rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  Cases_on `di` >> pure_rewrite_tac[optionTheory.option_case_def, pairTheory.pair_case_def] >> BETA_TAC >>
  map_every qid_spec_tac [`b'`, `x'`, `b`] >>
  rpt (FIRST [ho_match_mp_tac first_emission_bind >> conj_tac,
              ho_match_mp_tac first_emission_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC)
  >>~- ([`emit_op _ _ _ = _`],
    rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`emit_void _ _ _ = _`],
    rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`comp_return _ _ = _`], metis_tac[first_emission_return])
  >>~- ([`compile_word_copy_loop _ _ _ _ _ _ _ = _`], metis_tac[first_emission_word_copy_loop]) >>
  PairCases_on `x` >> pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
  metis_tac[first_emission_store_slots_family]
QED

Theorem first_emission_tuple_load_all[local]:
  !ce src tys off a x b. compile_tuple_load_all ce src tys off a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> Cases_on `tys` >>
  pure_rewrite_tac[compile_tuple_load_all_def, LET_THM] >> BETA_TAC
  >- metis_tac[first_emission_return] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  match_mp_tac cs_appends_bind >> conj_tac
  >- (rewrite_tac[contextTheory.compile_load_memory_def] >>
      IF_CASES_TAC >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
  gen_tac >> BETA_TAC >> irule cs_appends_bind >> simp[cs_appends_return] >>
  rw[cs_appends_def] >> metis_tac[stmt_list_helpers_labels, pairTheory.SND]
QED

Theorem first_emission_tuple_store_all[local]:
  !ce tys tgts vals a x b. compile_tuple_store_all ce tys tgts vals a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ho_match_mp_tac compile_tuple_store_all_ind >> rpt conj_tac
  >- (pure_rewrite_tac[compile_tuple_store_all_def] >> metis_tac[first_emission_return])
  >- suspend "base_target"
  >- (rpt gen_tac >> strip_tac >> pure_rewrite_tac[compile_tuple_store_all_def] >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[compile_tuple_store_all_def] >> metis_tac[first_emission_return]
QED

Resume first_emission_tuple_store_all[base_target]:
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[compile_tuple_store_all_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_get_target_ptr >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 10 (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[first_emission_return] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (IF_CASES_TAC >- metis_tac[first_emission_store_at_loc] >>
          rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
      metis_tac[first_emission_assign_value]) >>
  first_assum ACCEPT_TAC
QED
Finalise first_emission_tuple_store_all

Theorem first_emission_tuple_unpack[local]:
  !ce ty stage tgts src a x b. compile_tuple_unpack ce ty stage tgts src a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_tuple_unpack_def, LET_THM] >> BETA_TAC >>
  map_every qid_spec_tac [`b`, `x`, `a`] >> IF_CASES_TAC
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[first_emission_alloc_buffer] >>
          gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[first_emission_return] >>
          gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
          >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
          metis_tac[first_emission_return]) >>
      metis_tac[first_emission_return]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_tuple_load_all] >>
  metis_tac[first_emission_tuple_store_all]
QED

(* Complete routine cases before suspending the constructor-specific proofs. *)
val fe_simple_stmt =
  all_tac
  >>~- ([`compile_stmt _ (InLoop _ _) _ Break`], ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def] >> rpt strip_tac >>
    drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`compile_stmt _ (InLoop _ _) _ Continue`], ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def] >> rpt strip_tac >>
    drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`compile_stmt _ _ _ (Raise RaiseBare)`],
    pure_rewrite_tac[compile_stmt_def] >> rpt strip_tac >>
    drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`compile_stmt _ _ _ (Raise RaiseUnreachable)`],
    pure_rewrite_tac[compile_stmt_def] >> rpt strip_tac >>
    drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >>~- ([`compile_stmts _ _ _ []`],
    pure_rewrite_tac[compile_stmt_def] >> metis_tac[first_emission_return]);

val fe_unsupported_stmt =
  pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  metis_tac[first_emission_return];

val fe_none_external =
  Cases_on `ce.ce_ctor_exit_label` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (qabbrev_tac `nr = ce.ce_nonreentrant` >> PairCases_on `nr` >>
      pure_rewrite_tac[LET_THM, pairTheory.UNCURRY_DEF, pairTheory.FST, pairTheory.SND] >>
      CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >> metis_tac[first_emission_nonreentrant_unlock, first_emission_return]) >>
      rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[];

val fe_external_return =
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[first_emission_alloc_buffer] >>
          gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[first_emission_return] >>
          gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
          >- metis_tac[cj 1 first_emission_typed_memory_family] >>
          metis_tac[first_emission_return]) >>
      metis_tac[first_emission_return]) >>
  gen_tac >> BETA_TAC >> metis_tac[first_emission_external_return];

val fe_internal_return_env =
  pure_rewrite_tac[compile_internal_return_from_env_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (Cases_on `ce.ce_return_buf` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
      >- metis_tac[first_emission_return] >>
      rename1 `SOME loc` >> Cases_on `loc` >>
      pure_rewrite_tac[compileEnvTheory.var_location_case_def] >> BETA_TAC
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
          metis_tac[first_emission_return]) >>
      metis_tac[first_emission_return]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_return] >>
  gen_tac >> BETA_TAC >> metis_tac[first_emission_internal_return];

val fe_range_int_cases =
  Cases_on `l'` >> simp[cs_appends_return, cs_appends_emit_helpers] >>
  Cases_on `l` >> simp[cs_appends_return, cs_appends_emit_helpers];

val fe_range_literal_cases =
  Cases_on `end_e` >> simp[cs_appends_return, cs_appends_emit_helpers] >>
  fe_range_int_cases;

val fe_range_cases =
  all_tac >>~- ([`FLOOKUP _ _`],
    rpt (BasicProvers.TOP_CASE_TAC >> simp[cs_appends_emit_helpers])) >>
  Cases_on `start_e` >> simp[cs_appends_return, cs_appends_emit_helpers] >>
  fe_range_literal_cases;

val fe_array_copy_leaves =
  all_tac
  >>~- ([`cs_appends (compile_store_memory _ _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[first_emission_store_memory])
  >>~- ([`cs_appends (compile_word_copy_loop _ _ _ _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[compile_word_copy_loop_labels, pairTheory.SND])
  >>~- ([`cs_appends (compile_ptr_load _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[compile_ptr_load_labels, pairTheory.SND]) >>
  Cases_on `loc` >> simp[cs_appends_emit_helpers] >> rw[cs_appends_def]
  >>~- ([`compile_copy_memory _ _ _ _ = _`],
    drule first_emission_copy_memory >> simp[])
  >>~- ([`compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`],
    metis_tac[compile_imm_copy_to_memory_labels, pairTheory.SND]) >>
  metis_tac[compile_word_copy_loop_labels, pairTheory.SND];

val fe_array_suffix =
  all_tac
  >>~- ([`cs_appends (emit_jmp_if_not_terminated _)`],
    pure_rewrite_tac[emit_jmp_if_not_terminated_def] >>
    match_mp_tac cs_appends_bind >> conj_tac
    >- (rw[cs_appends_def] >> metis_tac[first_emission_get]) >>
    gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[cs_appends_return, cs_appends_emit_helpers])
  >>~- ([`cs_appends (compile_stmts _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[compile_stmt_labels, pairTheory.SND]) >>
  pop_assum kall_tac >> Cases_on `FLOOKUP body_cenv.ce_vars id` >>
  simp[cs_appends_emit_helpers] >> Cases_on `x` >> simp[cs_appends_emit_helpers] >>
  pure_rewrite_tac[compile_iter_elem_copy_def, contextTheory.compile_slot_to_memory_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac, IF_CASES_TAC] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_return]) >>
  fe_array_copy_leaves;

val fe_append_suffix =
  all_tac
  >>~- ([`cs_appends (compile_store_memory _ _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[first_emission_store_memory])
  >>~- ([`cs_appends (compile_word_copy_loop _ _ _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[compile_word_copy_loop_labels, pairTheory.SND]);

Theorem first_emission_compile_stmt:
  (!ce lc ty stmt a x b. compile_stmt ce lc ty stmt a = (x,b) ==>
   cs_extends a b /\
   ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
     a.cs_current_insts = b.cs_current_insts) \/
    (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce lc ty body a x b. compile_stmts ce lc ty body a = (x,b) ==>
   cs_extends a b /\
   ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
     a.cs_current_insts = b.cs_current_insts) \/
    (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac compile_stmt_ind >> all_tac >> rpt conj_tac
  >- (pure_rewrite_tac[compile_stmt_def] >> metis_tac[first_emission_return])
  >- (ntac 4 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- metis_tac[first_emission_compile_expr] >> metis_tac[first_emission_return])
  >- suspend "annassign"
  >~ [`compile_stmt _ _ _ (Assign (BaseTarget _) _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (Assign (TupleTarget _) _)`] >- suspend "tuple_assign"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`compile_stmt _ _ _ (Raise (RaiseReason _))`] >- suspend "raise_reason"
  >~ [`compile_stmt _ _ _ (Return (SOME _))`] >- suspend "return_value"
  >~ [`compile_stmt _ _ _ (Return NONE)`] >- suspend "return_none"
  >~ [`compile_stmt _ _ _ (Assert _ AssertBare)`] >- suspend "assert_bare"
  >~ [`compile_stmt _ _ _ (Assert _ AssertUnreachable)`] >- suspend "assert_unreachable"
  >~ [`compile_stmt _ _ _ (Assert _ (AssertReason _))`] >- suspend "assert_reason"
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- suspend "if_stmt"
  >~ [`compile_stmts _ _ _ (_::_)`] >- suspend "cons_stmt"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- suspend "log_stmt"
  >~ [`compile_stmt _ _ _ (Append _ _)`] >- suspend "append_stmt"
  >~ [`compile_stmt _ _ _ (For _ _ (Range _ _) _ _)`] >- suspend "range_stmt"
  >~ [`compile_stmt _ _ _ (For _ _ (Array _) _ _)`] >- suspend "array_stmt"
  >~ [`compile_stmt _ NoLoop _ Break`] >- (ntac 2 gen_tac >> fe_unsupported_stmt)
  >~ [`compile_stmt _ NoLoop _ Continue`] >- (ntac 2 gen_tac >> fe_unsupported_stmt)
  >~ [`compile_stmt _ _ _ (Raise (RaiseCustomError _))`] >- (ntac 4 gen_tac >> fe_unsupported_stmt)
  >~ [`compile_stmt _ _ _ (Assert _ (AssertCustomError _))`] >- (ntac 5 gen_tac >> fe_unsupported_stmt) >>
  fe_simple_stmt
QED

Resume first_emission_compile_stmt[annassign]:
  ntac 6 gen_tac >> pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[first_emission_local_alloca] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_compile_expr] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[first_emission_return, first_emission_unwrap_value]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_return] >>
  gen_tac >> BETA_TAC >>
  Cases_on `FLOOKUP ce.ce_vars id` >> pure_rewrite_tac[optionTheory.option_case_def]
  >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  BETA_TAC >> Cases_on `x` >> pure_rewrite_tac[compileEnvTheory.var_location_case_def] >> BETA_TAC >>
  rpt (IF_CASES_TAC)
  >>~- ([`emit_void _ _ _ = _`],
    rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  metis_tac[first_emission_assign_value]
QED


Resume first_emission_compile_stmt[assign]:
  ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (match_mp_tac first_emission_get_target_ptr >> metis_tac[first_emission_compile_expr]) >>
      gen_tac >> BETA_TAC >> metis_tac[first_emission_store_at_loc]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_compile_expr] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_get_target_ptr >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 3 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_return] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_unwrap_value] >>
  gen_tac >> BETA_TAC >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_return] >> gen_tac >> BETA_TAC) >>
  Cases_on `dst_loc_opt` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  metis_tac[first_emission_assign_value]
QED

Resume first_emission_compile_stmt[raise_reason]:
    ntac 4 gen_tac >> pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
    ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_reason_message] >>
    gen_tac >> BETA_TAC >> metis_tac[first_emission_revert_with_reason]
QED

Resume first_emission_compile_stmt[augassign]:
  ntac 7 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_get_target_ptr >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_return] >> gen_tac >> BETA_TAC) >>
  Cases_on `dst_loc_opt` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  ntac 2 (pure_once_rewrite_tac[comp_bind_def] >>
    pure_rewrite_tac[comp_return_def, LET_THM, pairTheory.pair_case_def, pairTheory.UNCURRY_DEF] >> BETA_TAC >>
    CONV_TAC (DEPTH_CONV ETA_CONV)) >>
  Cases_on `x` >> pure_rewrite_tac[data_location_case_def] >> BETA_TAC >> (
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_binop] >>
  gen_tac >> BETA_TAC >> rpt strip_tac >>
  drule_at Any (cj 2 first_emission_emit_helpers) >> simp[] >> metis_tac[])
QED

Resume first_emission_compile_stmt[return_value]:
  ntac 4 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  Cases_on `ce.ce_return_pc` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- fe_external_return >>
  Cases_on `x` >> pure_rewrite_tac[compileEnvTheory.var_location_case_def] >> BETA_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
      gen_tac >> BETA_TAC >> fe_internal_return_env)
  >- fe_external_return
  >- fe_external_return
  >- fe_external_return >>
  fe_internal_return_env
QED


Resume first_emission_compile_stmt[tuple_assign]:
    ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
    ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_compile_expr] >>
    gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_unwrap_value] >>
    gen_tac >> BETA_TAC >> metis_tac[first_emission_tuple_unpack]
QED

Resume first_emission_compile_stmt[return_none]:
  ntac 3 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
  Cases_on `ce.ce_return_pc` >> pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- fe_none_external >>
  Cases_on `x` >> pure_rewrite_tac[compileEnvTheory.var_location_case_def] >> BETA_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
      gen_tac >> BETA_TAC >> rpt strip_tac >>
      drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[])
  >- fe_none_external
  >- fe_none_external
  >- fe_none_external >>
  rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]
QED


Resume first_emission_compile_stmt[assert_bare]:
  ntac 4 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_counters] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

Resume first_emission_compile_stmt[assert_unreachable]:
  ntac 4 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_counters] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

Resume first_emission_compile_stmt[assert_reason]:
  ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_counters] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return]) >>
  rw[cs_appends_def] >>
  metis_tac[first_emission_reason_message, first_emission_revert_with_reason]
QED

Resume first_emission_compile_stmt[if_stmt]:
  ntac 6 gen_tac >> strip_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >>
  ntac 3 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_counters] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, IF_CASES_TAC, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
  >>~- ([`cs_appends (compile_stmts _ _ _ _)`],
    rw[cs_appends_def] >> first_x_assum drule >> simp[]) >>
  pure_rewrite_tac[emit_jmp_if_not_terminated_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac, gen_tac, IF_CASES_TAC] >>
    BETA_TAC >> simp[cs_appends_return, cs_appends_emit_helpers, cs_appends_prims]) >>
  rw[cs_appends_def] >> metis_tac[first_emission_get]
QED

Resume first_emission_compile_stmt[cons_stmt]:
  ntac 5 gen_tac >> strip_tac >> pure_rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_get] >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (Cases_on `stmt` >> pure_rewrite_tac[declare_stmt_local_def] >>
      metis_tac[first_emission_return, first_emission_declare_local]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_ignore_bind >>
  metis_tac[]
QED

Resume first_emission_compile_stmt[log_stmt]:
  ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
  Cases_on `ce.ce_event_info (nsid_to_string event_id)` >>
  pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  PairCases_on `x` >> pure_rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC >>
  ntac 2 (pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC) >>
  ntac 4 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_log_eval_all, first_emission_return] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_log_topic_ops] >>
  gen_tac >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_return] >> gen_tac >> BETA_TAC) >>
  IF_CASES_TAC
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_alloc_buffer] >>
  gen_tac >> BETA_TAC >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_return, cs_appends_emit_helpers]) >>
  rw[cs_appends_def] >>
  metis_tac[first_emission_log_store_data, compile_alloc_buffer_labels,
            compile_abi_encode_labels, pairTheory.SND]
QED

Resume first_emission_compile_stmt[range_stmt]:
  ntac 9 gen_tac >> strip_tac >>
  `!s e r n signed. cs_appends (compile_range_bound_checks s e r n signed)` by
    (pure_rewrite_tac[compile_range_bound_checks_def] >> rpt gen_tac >>
     rpt (FIRST [irule cs_appends_bind >> conj_tac,
                 irule cs_appends_ignore_bind >> conj_tac, gen_tac, IF_CASES_TAC] >> BETA_TAC >>
          simp[cs_appends_emit_helpers])) >>
  pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
    gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_declare_local] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[first_emission_local_alloca] >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_counters] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return])
  >>~- ([`cs_appends (compile_stmts _ _ _ _)`],
    rw[cs_appends_def] >> metis_tac[compile_stmt_labels, pairTheory.SND])
  >>~- ([`cs_appends (emit_jmp_if_not_terminated _)`],
    pure_rewrite_tac[emit_jmp_if_not_terminated_def] >>
    match_mp_tac cs_appends_bind >> conj_tac
    >- (rw[cs_appends_def] >> metis_tac[first_emission_get]) >>
    gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[cs_appends_return, cs_appends_emit_helpers]) >>
  fe_range_cases
QED


Resume first_emission_compile_stmt[array_stmt]:
  ntac 8 gen_tac >> strip_tac >>
  pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_compile_expr] >>
  gen_tac >> BETA_TAC >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_return] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[first_emission_ptr_load, first_emission_return]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_declare_local] >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[first_emission_local_alloca] >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
    >- metis_tac[first_emission_counters] >> gen_tac >> BETA_TAC) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac, IF_CASES_TAC] >> BETA_TAC >>
       simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]) >>
  fe_array_suffix
QED


Resume first_emission_compile_stmt[append_stmt]:
  ntac 5 gen_tac >> pure_rewrite_tac[compile_stmt_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[first_emission_compile_expr]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >- metis_tac[first_emission_return] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[first_emission_alloc_buffer] >>
      gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_ignore_bind >>
      metis_tac[first_emission_store_memory, first_emission_return]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[first_emission_return] >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac first_emission_strong >>
  pure_rewrite_tac[compile_dynarray_append_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (Cases_on `infer_array_location ce (target_to_expr target)` >>
      pure_rewrite_tac[load_opc_for_def] >> rpt strip_tac >>
      drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> BETA_TAC >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac, IF_CASES_TAC] >> BETA_TAC >>
       simp[cs_appends_return, cs_appends_emit_helpers]) >>
  fe_append_suffix
QED


Finalise first_emission_compile_stmt

(* Ensure the public mutual boundary is fully discharged. *)
val _ = if null (Thm.hyp first_emission_compile_stmt) then ()
        else raise Fail "first_emission_compile_stmt has undischarged hypotheses";
