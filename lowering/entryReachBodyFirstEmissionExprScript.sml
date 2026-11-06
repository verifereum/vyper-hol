Theory entryReachBodyFirstEmissionExpr
Ancestors
  entryReachBodyFirstEmissionExprSupport entryReachBodyFirstEmissionSupport
  compilerFirstEmission externalEntryShape exprOperandVar
  exprLowering exprCallBounds compileEnv fragExec emitHelper venomInst finite_map list

Theorem first_emission_expr_toplevelname[local]:
  !f g h ce ty t ns a x b.
  compile_expr_body f g h ce ty (TopLevelName t ns) a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars ns` >> simp[]
  >- (pairarg_tac >> simp[] >> rpt strip_tac >> gvs[] >>
      imp_res_tac first_emission_emit_helpers >> gvs[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt strip_tac >> gvs[cs_extends_refl] >>
  pairarg_tac >> gvs[] >> imp_res_tac first_emission_emit_helpers >> gvs[]
QED

Theorem first_emission_dynarray_pop[local]:
  !op ws sz ctor imm loc a x b.
  compile_dynarray_pop op ws sz ctor imm loc a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> pure_rewrite_tac[compile_dynarray_pop_def, LET_THM] >>
  BETA_TAC >> map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[first_emission_ptr_load] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [simp[cs_appends_emit_helpers] >> NO_TAC,
              irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC) >>
  rw[cs_appends_def] >>
  metis_tac[compile_ptr_store_labels, pairTheory.SND]
QED

Theorem first_emission_expr_pop[local]:
  (!ce ty e a x b. f ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !g h ce ty t tgt a x b.
  compile_expr_body f g h ce ty (Pop t tgt) a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_pair_let >>
  (conj_tac >- (drule first_emission_get_target_ptr >> metis_tac[]) >> qx_gen_tac `v`) >>
  PairCases_on `v` >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >>
  (conj_tac >- metis_tac[first_emission_dynarray_pop] >> gen_tac) >>
  simp[cs_extends_refl]
QED

Theorem first_emission_expr_structlit[local]:
  (!ce ty e s. cs_extends s (SND (f ce ty e s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (f ce ty e s)))) ==>
  !g h ce ty t ns fields a x b.
  compile_expr_body f g h ce ty (StructLit t ns fields) a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  imp_res_tac first_emission_alloc_buffer >>
  `cs_extends st2 b` by metis_tac[compile_struct_lit_labels, pairTheory.SND] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  rpt strip_tac >> irule first_emission_preserved >>
  qexistsl_tac [`st2`, `b`] >> simp[]
QED

Theorem first_emission_expr_ifexp[local]:
  (!ce ty e a x b. f ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce ty e. cs_appends (f ce ty e)) ==>
  !g h ce ty t c et ee a x b.
  compile_expr_body f g h ce ty (IfExp t c et ee) a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_pair_let >>
  (conj_tac >- (ho_match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac first_emission_pair_let >>
  (conj_tac >- metis_tac[first_emission_fresh] >> gen_tac) >>
  ntac 3 (ho_match_mp_tac first_emission_pair_let >>
          (conj_tac >- metis_tac[first_emission_counters] >> gen_tac)) >>
  rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> imp_res_tac first_emission_emit_helpers >> gvs[]) >>
  `!ce rt at vv. cs_appends (compile_ifexp_arm ce rt at vv)` by
    (rw[cs_appends_def] >> metis_tac[compile_ifexp_arm_labels, pairTheory.SND]) >>
  gen_tac >> BETA_TAC >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [simp[cs_appends_emit_helpers, cs_appends_prims] >> NO_TAC,
              irule cs_appends_bind >> conj_tac, gen_tac] >>
       BETA_TAC >> CONV_TAC (DEPTH_CONV ETA_CONV)) >>
  rw[cs_appends_def] >> Cases_on `is_word_type (expr_type (IfExp t c et ee))` >>
  gvs[cs_extends_refl]
QED

Theorem first_emission_expr_child_callback[local]:
  (!ce ty e a x b. expr_size e < bound /\ f ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce ty e a x b. expr_child_callback bound f ce ty e a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `expr_size e < bound` >> simp[expr_child_callback_def]
  >- metis_tac[] >>
  rewrite_tac[invalid_expr_call_def, LET_THM] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >> imp_res_tac first_emission_emit_helpers >> gvs[]
QED

Theorem first_emission_builtin_child_callback[local]:
  (!ce rt ty bi es a x b. list_size expr_size es < bound /\ g ce rt ty bi es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce rt ty bi es a x b. builtin_child_callback bound g ce rt ty bi es a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `list_size expr_size es < bound` >> simp[builtin_child_callback_def]
  >- metis_tac[] >>
  rewrite_tac[invalid_expr_call_def, LET_THM] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >> imp_res_tac first_emission_emit_helpers >> gvs[]
QED

Theorem first_emission_type_child_callback[local]:
  (!ce vt ty tb rt es a x b. list_size expr_size es < bound /\ h ce vt ty tb rt es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !ce vt ty tb rt es a x b. type_child_callback bound h ce vt ty tb rt es a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `list_size expr_size es < bound` >> simp[type_child_callback_def]
  >- metis_tac[] >>
  rewrite_tac[invalid_expr_call_def, LET_THM] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[] >> imp_res_tac first_emission_emit_helpers >> gvs[]
QED


Theorem first_emission_expr_builtin[local]:
  (!ce rt ty bi es a x b. g ce rt ty bi es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !f h ce ty t bi es a x b.
  compile_expr_body f g h ce ty (Builtin t bi es) a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> ntac 8 gen_tac >>
  qspec_then `\r. !x b. r = (x,b) ==> cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))`
    (ho_match_mp_tac o BETA_RULE) compiler_expr_builtin_pred >>
  BETA_TAC >> rpt conj_tac >>
  metis_tac[first_emission_mod_names, first_emission_powmod256_names]
QED
