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

Theorem first_emission_dynarray_to_storage[local]:
  !src dst ew em tr a x b. compile_dynarray_to_storage src dst ew em tr a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >>
  `!src dst n ll sl ctor. cs_appends (compile_word_copy_loop src dst n ll sl ctor)` by
    (rw[cs_appends_def] >> metis_tac[compile_word_copy_loop_labels, pairTheory.SND]) >>
  pure_rewrite_tac[contextTheory.compile_dynarray_to_storage_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac, IF_CASES_TAC] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_prims, cs_appends_return])
QED

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
  metis_tac[first_emission_dynarray_to_storage]
QED
