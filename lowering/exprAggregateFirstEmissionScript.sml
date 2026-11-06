(* Aggregate constructors: preserve callback boundaries, then stop at ADD. *)
Theory exprAggregateFirstEmission
Ancestors
  exprValueFirstEmission contextFirstEmission compilerFirstEmission
  entryConditionalFirstEmission exprLowering fragExec compileEnv emitHelper
  venomInst context

val aggregate_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM];
fun aggregate_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) aggregate_append_simps],
    (rename1 `cs_appends (unwrap_value _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_unwrap_value]),
    (rename1 `cs_appends (compile_store_memory _ _ _ _ _)` >>
      simp[cs_appends_def] >> metis_tac[first_emission_store_memory]),
    (rename1 `cs_appends (lower_value _ _ _ _)` >>
      rewrite_tac[lower_value_def] >> aggregate_append_tac),
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- aggregate_append_tac >> rpt gen_tac >> aggregate_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> aggregate_append_tac]) g;
fun aggregate_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> aggregate_append_tac) >>
   fs[cs_appends_def]) g;
fun aggregate_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) g;

Theorem cs_appends_make_tuple[local]:
  (!ty e. cs_appends (cfn ce ty e)) ==>
  !es buf off. cs_appends (compile_make_tuple cfn ce es buf off)
Proof
  strip_tac >> Induct >> rpt gen_tac >>
  simp_tac bool_ss [compile_make_tuple_def, LET_THM] >> aggregate_append_tac
QED

Theorem cs_appends_make_array_elems[local]:
  (!ty e. cs_appends (cfn ce ty e)) ==>
  !es ty sz lw buf idx. cs_appends (compile_make_array_elems cfn ce es ty sz lw buf idx)
Proof
  strip_tac >> Induct >> rpt gen_tac >>
  simp_tac bool_ss [compile_make_array_elems_def, LET_THM] >> aggregate_append_tac
QED

Theorem first_emission_make_tuple:
  (!ty e. cs_appends (cfn ce ty e)) /\
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_make_tuple cfn ce es buf off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `es`
  >- (rewrite_tac[compile_make_tuple_def] >> metis_tac[first_emission_return]) >>
  `!es buf off. cs_appends (compile_make_tuple cfn ce es buf off)` by
    (match_mp_tac cs_appends_make_tuple >> simp[]) >>
  simp_tac bool_ss [compile_make_tuple_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[listTheory.MEM] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- aggregate_emit_tac >> aggregate_tail_tac
QED

Theorem first_emission_make_array_elems:
  (!ty e. cs_appends (cfn ce ty e)) /\
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_make_array_elems cfn ce es ty sz lw buf idx a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `es`
  >- (rewrite_tac[compile_make_array_elems_def] >> metis_tac[first_emission_return]) >>
  `!es ty sz lw buf idx. cs_appends (compile_make_array_elems cfn ce es ty sz lw buf idx)` by
    (match_mp_tac cs_appends_make_array_elems >> simp[]) >>
  simp_tac bool_ss [compile_make_array_elems_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[listTheory.MEM] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- aggregate_emit_tac >> aggregate_tail_tac
QED

Theorem first_emission_make_array:
  (!ty e. cs_appends (cfn ce ty e)) /\
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_make_array cfn ce es ty sz lw buf a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[compile_make_array_def] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (Cases_on `lw` >> simp_tac bool_ss []
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
      metis_tac[first_emission_return]) >>
  match_mp_tac first_emission_make_array_elems >> conj_tac
  >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Theorem first_emission_multi_exprs:
  !es.
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_multi_exprs cfn ce es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct
  >- (simp_tac bool_ss [compile_multi_exprs_def] >> metis_tac[first_emission_return]) >>
  gen_tac >> strip_tac >> simp_tac bool_ss [compile_multi_exprs_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum match_mp_tac >> metis_tac[listTheory.MEM]) >>
  gen_tac >> metis_tac[first_emission_return]
QED

Theorem cs_appends_concat[local]:
  (!ty e. cs_appends (cfn ce ty e)) ==>
  !es data_ptr infos off. cs_appends (compile_concat cfn ce es data_ptr infos off)
Proof
  strip_tac >> Induct >> rpt gen_tac
  >- (rewrite_tac[compile_concat_def] >> aggregate_append_tac) >>
  Cases_on `infos`
  >- (rewrite_tac[compile_concat_def] >> aggregate_append_tac) >>
  PairCases_on `h'` >> simp_tac bool_ss [compile_concat_def] >>
  IF_CASES_TAC >> aggregate_append_tac
QED

Theorem first_emission_concat:
  (!ty e. cs_appends (cfn ce ty e)) /\
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_concat cfn ce es data_ptr infos off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `es`
  >- (rewrite_tac[compile_concat_def] >> metis_tac[first_emission_return]) >>
  Cases_on `infos`
  >- (rewrite_tac[compile_concat_def] >> metis_tac[first_emission_return]) >>
  `!es dp infos off. cs_appends (compile_concat cfn ce es dp infos off)` by
    (match_mp_tac cs_appends_concat >> simp[]) >>
  PairCases_on `h'` >> simp_tac bool_ss [compile_concat_def] >> IF_CASES_TAC >>
  (ho_match_mp_tac first_emission_bind >> conj_tac
   >- (match_mp_tac first_emission_lower_value >> metis_tac[listTheory.MEM]) >>
   gen_tac >> ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- aggregate_emit_tac >> aggregate_tail_tac)
QED

Theorem cs_appends_struct_lit[local]:
  (!ty e. cs_appends (cfn ce ty e)) ==>
  !fields ty buf off. cs_appends (compile_struct_lit cfn ce ty fields buf off)
Proof
  strip_tac >> Induct >> rpt gen_tac
  >- (rewrite_tac[compile_struct_lit_def] >> aggregate_append_tac) >>
  PairCases_on `h` >> simp_tac bool_ss [compile_struct_lit_def, LET_THM] >>
  aggregate_append_tac
QED

Theorem first_emission_struct_lit:
  (!ty e. cs_appends (cfn ce ty e)) /\
  (!e a x b. MEM e (MAP SND fields) /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_struct_lit cfn ce ty fields buf off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> Cases_on `fields`
  >- (rewrite_tac[compile_struct_lit_def] >> metis_tac[first_emission_return]) >>
  `!fields ty buf off. cs_appends (compile_struct_lit cfn ce ty fields buf off)` by
    (match_mp_tac cs_appends_struct_lit >> simp[]) >>
  PairCases_on `h` >> simp_tac bool_ss [compile_struct_lit_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (fs[listTheory.MAP, listTheory.MEM] >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- aggregate_emit_tac >> aggregate_tail_tac
QED
