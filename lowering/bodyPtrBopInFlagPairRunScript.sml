Theory bodyPtrBopInFlagPairRun
Ancestors bodyPtrBopInFlagRobust bodyPtrBopContinuation bodyPtrBopEntry
  bodyPtrBopOperandContract bodyPtrDefs loweringPosts exprSimDefs exprSimProps
  vyperTypeSystem vyperValue vyperTyping loweringSlice exprBopSimProps valueEncoding compileEnv

Theorem membership_flag_typed_inputs:
  (bop = In \/ bop = NotIn) /\ well_typed_binop ann bop ty (FlagT fid) /\
  evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv (FlagT fid) = SOME tv2 /\ value_has_type tv2 v2 ==>
  ?m. value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\ m <= 256
Proof
  strip_tac >> gvs[well_typed_binop_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem membership_flag_pair_run:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
        (INL v1,es1)) /\
  (?gs. bind (eval_expr cx e2) (read_result cx) (es1 with gas_obs := gs) =
        (INL v2,es2)) /\
  bop_operand_post d ctx func cenv cx e1 es ca c1 x t0 G0 tn0
    v1 es1 t1 G1 tn1 /\
  bop_operand_post d ctx func cenv cx e2 es1 c1 c2 y t1 G1 tn1
    v2 es2 t2 G2 tn2 /\
  (bop = In \/ bop = NotIn) /\ expr_type e2 = FlagT fid /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) c2 = (op,cz) /\
  (!z. x = Var z ==> not_fresh_at c1 z) /\ (!l. x <> Label l) /\
  (!z. x = Var z ==> not_fresh_at c2 z) /\
  (!z. y = Var z ==> not_fresh_at c2 z) ==>
  ?v t. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 es2 = INL v /\
    word_value v /\ run_inst_seq (emitted_insts c2 cz) t2 = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule bop_pair_source_facts >>
  disch_then (qspecl_then [`v2`, `v1`, `es2`, `es1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule_all bop_pair_word_inputs >> strip_tac >>
  `?m. value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\ m <= 256` by
    (irule membership_flag_typed_inputs >> simp[] >> metis_tac[]) >>
  `word_value v1 /\ word_value v2` by
    (conj_tac
     >- (qpat_x_assum `value_has_type (FlagTV m) v1` mp_tac >>
         Cases_on `v1` >> simp[value_has_type_def, word_value_def]) >>
     qpat_x_assum `value_has_type (FlagTV m) v2` mp_tac >>
     Cases_on `v2` >> simp[value_has_type_def, word_value_def]) >>
  `eval_operand x t1 = SOME (val_to_w256 v1) /\
   eval_operand y t2 = SOME (val_to_w256 v2)` by
    (gvs[bop_operand_post_def, expr_post_def] >>
     metis_tac[expr_val_rel_word, optionTheory.IS_SOME_EXISTS]) >>
  irule membership_flag_source_run_robust >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`if bop = Exp then expr_int_literal e1 else NONE`,
        `if bop = Exp then expr_int_literal e2 else NONE`, `expr_type e1`, `x`, `y`] >>
      simp[]) >>
  metis_tac[]
QED
