(* Counted binary operator producer and its source facts. *)
Theory exprBopBitwise
Ancestors
  exprBopSimDefs exprBopSimProps exprSimBopTyped exprBopStraight
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt  freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib

Theorem bop_result_bitwise_pairs[local]:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) ==>
  ((?i1 i2. v1 = IntV i1 /\ v2 = IntV i2) \/
   (?b1 b2. v1 = BoolV b1 /\ v2 = BoolV b2) \/
   (?n1 n2. v1 = FlagV n1 /\ v2 = FlagV n2))
Proof
  strip_tac >> gvs[] >>
  fs[bop_result_def, evaluate_builtin_def] >>
  Cases_on `v1` >> gvs[evaluate_binop_def, expr_res_ok_def] >>
  gvs[AllCaseEqs()]
QED


(* And, Or and XOr on two values give the word operation on their words.
   On integers the source checks the result against the type's bound;
   operands within it keep the result within it, so the check never
   fails. *)
Theorem bop_result_bitwise:
  !cx ann bop v1 v2 es.
    (bop = And \/ bop = Or \/ bop = XOr) /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) ==>
    ?v. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
        val_to_w256 v =
          (if bop = And then word_and else if bop = Or then word_or
           else word_xor) (val_to_w256 v1) (val_to_w256 v2)
Proof
  rpt gen_tac >> strip_tac >>
  `(?i1 i2. v1 = IntV i1 /\ v2 = IntV i2) \/
   (?b1 b2. v1 = BoolV b1 /\ v2 = BoolV b2) \/
   (?n1 n2. v1 = FlagV n1 /\ v2 = FlagV n2)` by
    (irule bop_result_bitwise_pairs >> simp[] >> metis_tac[]) >>
  gvs[] >>
  qabbrev_tac
    `u = case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0` >>
  `!i1 i2. within_int_bound u i1 /\ within_int_bound u i2 ==>
     within_int_bound u (int_and i1 i2) /\ within_int_bound u (int_or i1 i2) /\
     within_int_bound u (int_xor i1 i2)` by
    simp[int_and_def, int_or_def, int_xor_def, within_int_bound_int_bitwise] >>
  (* one operation at a time, each unfolding a third of the value pairs *)
  gvs[] >>
  fs[bop_result_def, evaluate_builtin_def] >>
  gvs[evaluate_binop_def, expr_res_ok_def] >>
  gvs[bounded_int_op_def, val_to_w256_def, word_value_def,
      i2w_int_and, i2w_int_or, i2w_int_xor]
  >>~- ([`(if _ then 1w else 0w) = _`],
         rpt IF_CASES_TAC >> gvs[] >>
         simp[WORD_AND_CLAUSES, WORD_OR_CLAUSES, WORD_XOR_CLAUSES]) >>
  qmatch_goalsub_abbrev_tac `n2w (Num z)` >>
  `~(z < 0)` by
    simp[Abbr `z`, int_and_def, int_or_def, int_xor_def, int_bitwise_neg] >>
  `(n2w (Num z) : bytes32) = i2w z` by simp[i2w_def] >>
  pop_assum SUBST1_TAC >>
  simp[Abbr `z`, i2w_int_and, i2w_int_or, i2w_int_xor, i2w_pos]
QED

Theorem straight_fresh_compile_bitwise:
  (bop = And \/ bop = Or \/ bop = XOr) ==>
  straight_fresh (compile_binop bop x y ty bl el)
Proof
  strip_tac >> gvs[compile_binop_def] >>
  irule straight_fresh_emit_op >> simp[fresh_write_op_def]
QED

Theorem compile_bitwise_run:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  compile_binop bop x y ty bl el sa = (op, sb) /\
  fresh_vars_wrt sa ss /\
  eval_operand x ss = SOME w1 /\
  eval_operand y ss = SOME w2 ==>
  ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
        eval_operand op ss' = SOME
          ((if bop = And then word_and else if bop = Or then word_or else word_xor) w1 w2)
Proof
  strip_tac >> gvs[compile_binop_def] >>
  drule emit_op_pure2_correct >>
  disch_then drule >> disch_then drule >>
  disch_then drule
  >- (disch_then (qspec_then `word_and` mp_tac) >>
      simp[step_AND] >> metis_tac[])
  >- (disch_then (qspec_then `word_or` mp_tac) >>
      simp[step_OR] >> metis_tac[]) >>
  disch_then (qspec_then `word_xor` mp_tac) >>
  simp[step_XOR] >> metis_tac[]
QED

(* The lowering emits the word operation, one instruction. *)
Theorem compile_bitwise_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0.
    (bop = And \/ bop = Or \/ bop = XOr) /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  irule binop_frag_straight >>
  conj_tac >- metis_tac[straight_fresh_compile_bitwise] >>
  disch_tac >>
  drule_all bop_result_bitwise >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rpt strip_tac >>
  drule_all compile_bitwise_run >> simp[]
QED

(* ===== Flag membership ===== *)


