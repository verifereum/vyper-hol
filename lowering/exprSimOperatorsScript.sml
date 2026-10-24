(*
 * Expression simulation: the operators (#636, Operators)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the operators and
 * the conditional expression.
 *
 * TOP-LEVEL:
 *   compile_bop_case_sim     — a binary operator: on operands of
 *                              word_value_type by compile_bop_word_sim, the
 *                              rest by compile_bop_other_sim
 *   compile_bop_word_sim     — compile_bop_sim (exprSimOps) from the
 *                              operands' expr_sim_ok and binop_frag_typed
 *   expr_sim_pre_bop         — the operands of a well-typed binary operator
 *                              meet expr_sim_pre
 *   compile_not_sim, compile_neg_sim, compile_abs_sim — not, unary -, abs
 *   compile_ifexp_sim        — x if c else y
 *
 * Cheated, for the later #636 PRs:
 *   binop_frag_typed         — the operator's fragment on typed word
 *                              operands.  #692 proves it for the checked and
 *                              unchecked arithmetic, comparisons, min/max,
 *                              bit operations, flag membership and 256-bit
 *                              shifts (compile_checked_sim, ...); left are
 *                              ** and pow_mod (#572) and shifts of narrower
 *                              integers, which the type system admits
 *                              (well_typed_binop ShL/ShR) but the lowering
 *                              does not truncate (#572), and shifts by a
 *                              negative amount, where the source raises
 *                              and the lowering shifts.  Operators rows
 *                              2-5.
 *   compile_bop_other_sim    — == and != on address, bytesN and bytestrings
 *                              (msg.sender == owner lands here),
 *                              in and not in on arrays (#569), Operators
 *                              row 6
 *   compile_not_sim, compile_neg_sim (#572), compile_abs_sim — row 7
 *   compile_ifexp_sim        — row 9, aggregate ternaries per #561; also
 *                              row 8, the and/or chains (#556), which the
 *                              frontend desugars to nested IfExps
 *                              (translate_boolop).  Bop And/Or are the
 *                              bitwise & and |.
 *
 * Compile-side facts, cheated (the shape #674's compile_expr_shape
 * proves for the shape judgment):
 *   lower_value_word_shape   — lowering a word-typed expression only
 *                              appends, hands out its variables, and
 *                              returns a variable it handed out or a literal
 *   compile_binop_shape      — compile_binop only appends
 * compile_bop_word_sim rests on these two and on binop_frag_typed.  Both are
 * for word types only; the compound non-word cases need #674's
 * compile_expr_shape.
 *)

Theory exprSimOperators
Ancestors
  list finite_map
  fragExec exprSim exprSimHyps exprSimOps exprBopLowering loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTyping vyperTypeInvariants

(* ===== Compile-side facts ===== *)

Theorem lower_value_word_shape:
  !cenv ty e sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    is_word_type (expr_type e) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  cheat
QED

Theorem compile_binop_shape:
  !bop x y ty bl el sa op sb.
    compile_binop bop x y ty bl el sa = (op, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  cheat
QED

(* ===== Binary operators ===== *)

Theorem word_value_type_word:
  !t. word_value_type t ==>
      is_word_type t /\ ~is_ArrayT t /\ ~is_bytestring_type t
Proof
  Cases >> simp[word_value_type_def, is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt`) >>
  simp[is_word_type_def, is_bytestring_type_def]
QED

Theorem well_typed_binop_word_result:
  !ann bop t1 t2.
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 ==>
    is_word_type ann
Proof
  rpt strip_tac >> drule word_value_type_word >> strip_tac >>
  Cases_on `bop` >> gvs[well_typed_binop_def, is_word_type_def]
QED

Theorem binop_frag_typed:
  !ctx func cenv cx bop ann e1 e2 v1 v2 es0 tv1 tv2.
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop (expr_type e1) ann
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE)
      [expr_type e1; expr_type e2] v1 v2 es0
Proof
  cheat
QED

Theorem expr_sim_pre_bop:
  !cenv cx env ann bop e1 e2 es.
    expr_sim_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    expr_sim_pre cenv cx env e1 es /\
    !es'. expr_sim_inv cenv cx env es' ==> expr_sim_pre cenv cx env e2 es'
Proof
  rpt strip_tac
  >- gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def]
  >- (drule expr_sim_pre_builtin_arg >> disch_then irule >>
      gvs[expr_sim_pre_def]) >>
  drule expr_sim_pre_builtin_arg >> disch_then irule >> simp[]
QED

Theorem expr_sim_ok_apply:
  !ctx func cenv cx env ty e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    expr_sim ctx func cenv cx ty e es
Proof
  metis_tac[expr_sim_ok_def]
QED

Theorem compile_bop_word_sim:
  !cenv ann bop e1 e2.
    expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt strip_tac >> simp[expr_sim_ok_def] >> rpt strip_tac >>
  drule expr_sim_pre_bop >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `expr_sim_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `is_word_type (expr_type e1) /\ ~is_ArrayT (expr_type e1) /\
   ~is_bytestring_type (expr_type e1) /\
   is_word_type (expr_type e2) /\ ~is_ArrayT (expr_type e2) /\
   ~is_bytestring_type (expr_type e2)` by gvs[word_value_type_word] >>
  imp_res_tac well_typed_expr_type_evaluates >>
  `is_word_type ann` by (drule_all well_typed_binop_word_result >> simp[]) >>
  irule compile_bop_sim >> rpt conj_tac
  >~ [`binop_frag`]
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`, `INL (Value v1)`, `es1`]
        mp_tac expr_sim_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `Value v1` mp_tac) >> simp[] >> strip_tac >>
      rename1 `value_has_type tv1 v1` >>
      `expr_sim_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      conj_tac >- gvs[] >>
      conj_tac
      >- (rpt strip_tac >>
          qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1`, `INL tv`, `es2`] mp_tac
            expr_sim_pre_word_result >>
          impl_tac >- gvs[] >> strip_tac >> gvs[]) >>
      conj_tac
      >- metis_tac[expr_sim_ok_apply] >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1`, `INL (Value v2)`, `es2`]
        mp_tac expr_sim_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `Value v2` mp_tac) >> simp[] >>
      strip_tac >> rename1 `value_has_type tv2 v2` >> simp[] >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `e1`, `e2`,
                   `v1`, `v2`, `es2`, `tv1`, `tv2`] mp_tac binop_frag_typed >>
      impl_tac >- gvs[] >> simp[])
  >~ [`eval_expr cx e1 es = (INL _, _)`]
  >- (rpt strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`, `INL tv`, `es1`] mp_tac
        expr_sim_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >> gvs[])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >> drule lower_value_word_shape >> gvs[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >> drule lower_value_word_shape >> gvs[])
  >~ [`expr_sim`]
  >- metis_tac[expr_sim_ok_apply] >>
  gvs[]
QED

Theorem compile_bop_other_sim:
  !ctx func cenv cx env ty ann bop args es.
    expr_sim_below cenv (list_size expr_size args) /\
    expr_sim_pre cenv cx env (Builtin ann (Bop bop) args) es /\
    (!e1 e2. args = [e1; e2] ==>
             ~(word_value_type (expr_type e1) /\
               word_value_type (expr_type e2))) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) args) es
Proof
  cheat
QED

Theorem compile_bop_case_sim:
  !cenv ann bop args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) args)
Proof
  rpt strip_tac >>
  Cases_on `?e1 e2. args = [e1; e2] /\ word_value_type (expr_type e1) /\
                    word_value_type (expr_type e2)`
  >- (pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      `expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2` by
        metis_tac[expr_sim_below_mem, listTheory.MEM, expr_ok_def] >>
      irule compile_bop_word_sim >> fs[]) >>
  rw[expr_sim_ok_def] >> irule compile_bop_other_sim >>
  metis_tac[]
QED

(* A binary operator is lowered to a StackValue. *)
Theorem compile_bop_stack:
  !cenv ty ann bop args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann (Bop bop) args) sa =
              (StackValue t op, sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_bop, vyperASTTheory.expr_type_def] >>
  simp[Once compile_expr_def, LET_THM, as_stack_val_pair,
       pairTheory.UNCURRY] >>
  rw[] >>
  Cases_on `HD (TL args)` >>
  simp[pairTheory.UNCURRY] >>
  rename1 `Builtin _ bi _` >> Cases_on `bi` >> simp[]
QED

Theorem compile_bop_ok:
  !cenv ann bop args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_ok cenv (Builtin ann (Bop bop) args)
Proof
  rpt strip_tac >> irule expr_ok_stack >>
  simp[compile_bop_case_sim, compile_bop_stack] >>
  rpt strip_tac >> drule eval_expr_builtin_value >> simp[]
QED

(* ===== Unary operators ===== *)

Theorem compile_not_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Not args)
Proof
  cheat
QED

Theorem compile_neg_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Neg args)
Proof
  cheat
QED

Theorem compile_abs_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Abs args)
Proof
  cheat
QED

(* ===== Conditional expression ===== *)

Theorem compile_ifexp_sim:
  !cenv ann c e1 e2.
    expr_sim_below cenv (expr_size (IfExp ann c e1 e2)) ==>
    expr_vv_ok cenv (IfExp ann c e1 e2)
Proof
  cheat
QED
