(* Fresh-write shape of all total safe_pow branches. *)
Theory powerFragProps
Ancestors
  powerCheckedProps powerGuardProps exprSimArith exprSimOps freshWrites exprLowering
  exprLoweringProps compileEnv emitHelperProps valueEncoding vyperInterpreter
  vyperContext loweringSlice
  vyperValueOperation vyperValue vyperAST words integer_word integer

Theorem straight_fresh_safe_pow:
  !x y ty bl el. straight_fresh (compile_safe_pow x y ty bl el)
Proof
  rpt gen_tac >> simp[compile_safe_pow_def] >>
  Cases_on `bl` >> Cases_on `el` >> simp[clamp_and_return_def] >>
  rpt (FIRST [IF_CASES_TAC,
    irule straight_fresh_bind >> conj_tac,
    irule straight_fresh_ignore_bind >> conj_tac,
    gen_tac >> BETA_TAC,
    irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
    MATCH_ACCEPT_TAC straight_fresh_return,
    irule straight_fresh_compile_clamp])
QED

(* Coherent arithmetic simulation boundary: the two run outcomes below are
   supplied by checked_power_run, not an admitted arithmetic simulation. *)
Theorem binop_frag_power_run:
  type_to_int_bound ann = SOME u /\
  (!x y sa sb op ss.
    compile_binop Exp x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (i2w e) ==>
    (0 <= e /\ within_int_bound u (a ** Num e) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num e))) /\
    (e < 0 \/ ~within_int_bound u (a ** Num e) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')) ==>
  binop_frag ctx func cenv cx Exp ty ann bl el tys (IntV a) (IntV e) es0
Proof
  strip_tac >>
  qabbrev_tac `rr = a ** Num e` >>
  qabbrev_tac `ok = (0 <= e /\ within_int_bound u rr)` >>
  qabbrev_tac `msg = if e < 0 then "Exp~" else "bounded_int_op bound"` >>
  `bop_result cx ann Exp tys (IntV a) (IntV e) es0 =
    if ok then INL (IntV rr) else INR (Error (RuntimeError msg))` by
    (simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
          bounded_int_op_def, Abbr `ok`, Abbr `rr`, Abbr `msg`] >>
     Cases_on `e < 0` >> gvs[GSYM INT_NOT_LE] >> IF_CASES_TAC >> gvs[]) >>
  irule binop_frag_straight >> conj_tac
  >- simp[compile_binop_def, straight_fresh_safe_pow] >>
  strip_tac >> asm_rewrite_tac[] >> Cases_on `ok` >> asm_rewrite_tac[]
  >- (disj1_tac >> qexists_tac `IntV rr` >>
      simp[word_value_def, val_to_w256_def] >> rpt strip_tac >>
      first_x_assum drule_all >> simp[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `msg` >> simp[val_to_w256_def] >> rpt strip_tac >>
  first_x_assum drule_all >>
  fs[markerTheory.Abbrev_def, INT_NOT_LE] >> metis_tac[]
QED
