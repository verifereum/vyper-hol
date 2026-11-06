(* Arithmetic emits before any control-flow suffix. *)
Theory arithmeticFirstEmission
Ancestors
  compilerFirstEmission entryConditionalFirstEmission exprLowering
  builtinSimple fragExec compileEnv emitHelper venomInst context

val arith_append_simps =
  [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM];
fun arith_append_with extras g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) (extras @ arith_append_simps)],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- arith_append_with extras >> rpt gen_tac >> arith_append_with extras,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> arith_append_with extras,
    IF_CASES_TAC >> arith_append_with extras]) g;
val arith_append_tac = arith_append_with [];

Theorem arithmetic_clamp_appends[local]:
  cs_appends (compile_clamp v ty)
Proof
  simp_tac bool_ss [compile_clamp_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (srw_ss()) [] >> arith_append_tac
QED

Theorem arithmetic_return_clamp_appends[local]:
  cs_appends (clamp_and_return v ty)
Proof
  simp_tac bool_ss [clamp_and_return_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >>
  simp[arithmetic_clamp_appends, cs_appends_return]
QED

Theorem arithmetic_mul_check_appends[local]:
  cs_appends (compile_mul_overflow_check x y z s n)
Proof
  simp_tac bool_ss [compile_mul_overflow_check_def, LET_THM] >>
  arith_append_tac
QED

val arith_append_tac = arith_append_with
  [arithmetic_clamp_appends, arithmetic_return_clamp_appends,
   arithmetic_mul_check_appends];
fun arith_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun arith_tail_tac g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> arith_append_tac) >>
   fs[cs_appends_def]) g;
fun arith_strong_tac g =
  (FIRST [arith_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- arith_strong_tac >> arith_tail_tac,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- arith_strong_tac >> arith_tail_tac]) g;

Theorem first_emission_safe_add:
  !a x b. compile_safe_add v w ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_safe_add_def, LET_THM] >> arith_strong_tac
QED

Theorem first_emission_safe_sub:
  !a x b. compile_safe_sub v w ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_safe_sub_def, LET_THM] >> arith_strong_tac
QED

Theorem first_emission_safe_mul:
  !a x b. compile_safe_mul v w ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_safe_mul_def, LET_THM] >> arith_strong_tac
QED

Theorem first_emission_safe_div:
  !a x b. compile_safe_div v w ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_safe_div_def, LET_THM] >> arith_strong_tac
QED

Theorem first_emission_safe_decimal_div:
  !a x b. compile_safe_decimal_div v w d ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_safe_decimal_div_def, LET_THM] >> arith_strong_tac
QED

Theorem first_emission_safe_mod:
  !a x b. compile_safe_mod v w ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_safe_mod_def, LET_THM] >> arith_strong_tac
QED

Theorem first_emission_safe_pow:
  !a x b. compile_safe_pow v w ty bl el a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `bl` >- (
    Cases_on `el` >>
    simp_tac (srw_ss()) [compile_safe_pow_def, LET_THM] >>
    rpt IF_CASES_TAC >> arith_strong_tac) >>
  simp_tac (srw_ss()) [compile_safe_pow_def, LET_THM] >>
  IF_CASES_TAC >- (
    ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
    >- (IF_CASES_TAC
        >- (ho_match_mp_tac first_emission_strong >> arith_strong_tac) >>
        metis_tac[first_emission_return]) >>
    gen_tac >> arith_strong_tac) >>
  arith_strong_tac
QED

Theorem first_emission_compare:
  !a x b. compile_compare bop v w ty a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `bop` >> simp_tac (srw_ss()) [compile_compare_def, LET_THM] >>
  rpt IF_CASES_TAC >> arith_strong_tac
QED

Theorem first_emission_binop:
  !a x b. compile_binop bop v w ty bl el a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `bop` >> simp_tac (srw_ss()) [compile_binop_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  FIRST [FIRST (map MATCH_ACCEPT_TAC
    [first_emission_safe_add, first_emission_safe_sub,
     first_emission_safe_mul, first_emission_safe_div,
     first_emission_safe_decimal_div, first_emission_safe_mod,
     first_emission_safe_pow, first_emission_compare]),
    (simp_tac bool_ss [wrap_truncate_def, compile_select_def] >> arith_strong_tac)]
QED
