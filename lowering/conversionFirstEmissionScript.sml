(* Conversion no-op paths preserve code; checks and loads emit non-PHI. *)
Theory conversionFirstEmission
Ancestors
  compilerFirstEmission contextFirstEmission exprLowering fragExec
  compileEnv emitHelper venomInst context

fun conv_append_tac g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
       [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM]],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- conv_append_tac >> rpt gen_tac >> conv_append_tac,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> conv_append_tac,
    IF_CASES_TAC >> conv_append_tac]) g;
fun conv_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail st0 = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> conv_append_tac) >>
   fs[cs_appends_def]) g;
fun conv_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun conv_strong_tac g =
  (FIRST [conv_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- conv_strong_tac >> conv_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- conv_strong_tac >> conv_tail_tac]) g;

Theorem first_emission_int_clamp:
  !a x b. compile_int_clamp signed bits v a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `signed` >> simp_tac bool_ss [compile_int_clamp_def, LET_THM] >>
  conv_strong_tac
QED

Theorem first_emission_load_bytestring_as_word:
  opc <> PHI ==>
  !a x b. load_bytestring_as_word v opc a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> simp_tac bool_ss [load_bytestring_as_word_def] >> conv_strong_tac
QED

