(* Guarded operand premises for word builtin prefixes. *)
Theory s1PrefixGuardedWord
Ancestors
  s1PrefixPreds bodyFullPreds bodyFullExprGeneric s1PrefixBuiltinWord
  vyperAST vyperContext exprLoweringProps

Theorem word_builtin_expr_prefix_ok:
  !cx ty bt es.
  (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_prefix_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule word_builtin_sim_prefix >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          irule bodyFullExprGenericTheory.expr_vv_sim_stack_full >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          Cases_on `is_word_type (expr_type e)` >> simp[]) >>
      qexistsl_tac [`env`, `tops`] >> asm_rewrite_tac[]) >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[]
QED
