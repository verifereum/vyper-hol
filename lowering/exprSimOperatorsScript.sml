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
 *   compile_not_sim, compile_abs_sim — not and abs: exprSimUnop's
 *                              compile_unop_sim with compile_not_frag and
 *                              compile_abs_frag
 *   compile_neg_sim          — unary -
 *   compile_ifexp_sim        — x if c else y: compile_ifexp_word_sim for
 *                              word types, compile_ifexp_aggregate_sim for
 *                              the rest
 *
 * Cheated, for the later #636 PRs:
 *   binop_frag_typed         — from exprSimBinopFrag, where it rests on
 *                              cheats for ** and pow_mod and narrow or
 *                              negative shifts (#572), and >> of narrow
 *                              integers.  Operators rows 2-5.
 *   compile_bop_other_sim    — == and != on address, bytesN and bytestrings
 *                              (msg.sender == owner lands here),
 *                              in and not in on arrays (#569), Operators
 *                              row 6
 *   compile_neg_sim (#572)   — row 7; not and abs are proved
 *   compile_ifexp_aggregate_sim — row 9 for aggregate ternaries (#561,
 *                              #674); word ternaries are proved
 *                              (compile_ifexp_word_sim), and so are row 8's
 *                              and/or chains (#556), which the frontend
 *                              desugars to nested IfExps of type bool
 *                              (translate_boolop).  Bop And/Or are the
 *                              bitwise & and |.
 *
 * Compile-side facts:
 *   lower_value_word_shape   — lowering a well-typed word expression only
 *                              appends, hands out its variables, and
 *                              returns a variable it handed out or a literal
 *   compile_binop_shape      — compile_binop only appends
 * compile_bop_word_sim rests on these two and on binop_frag_typed, and
 * compile_ifexp_word_sim, compile_not_sim, compile_abs_sim and
 * exprSimConvert's compile_convert_word_sim on lower_value_word_shape.
 *
 * Helpers: expr_sim_pre_lower_value_word_shape.
 *)

Theory exprSimOperators
Ancestors
  list finite_map
  fragExec exprSim exprSimHyps exprSimOps exprSimIfExp exprSimBinopFrag
  exprSimUnop
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness

(* ===== Compile-side facts ===== *)

(* The typing hypotheses keep a pointer from cenv out of the value.
   unwrap_value loads only a word, and some conversions return their
   operand: for an ill-typed e, convert(s, uint256) with s a struct lowers
   to the pointer to s (ConvIdentity); for a local of the ill-formed type
   bytes40, which the Name typing rule admits, convert(x, bytes32) lowers
   to the pointer to x (ConvBytesMToBytesM). *)
Theorem lower_value_word_shape:
  !cenv env ty e sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    is_word_type (expr_type e) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  rpt gen_tac >> strip_tac >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  drule lower_value_word_safe_operand >>
  disch_then (qspec_then `env` mp_tac) >>
  disch_then drule_all >> simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem compile_binop_shape:
  !bop x y ty bl el sa op sb.
    compile_binop bop x y ty bl el sa = (op, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule exprLoweringPropsTheory.compile_binop_grows >> simp[]
QED

(* lower_value_word_shape for an operand that meets expr_sim_pre, which
   carries both typing hypotheses. *)
Theorem expr_sim_pre_lower_value_word_shape:
  !cenv cx env e es ty sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env e` by fs[expr_sim_pre_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[expr_sim_pre_var_types_well_formed] >>
  drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
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

Theorem expr_sim_pre_bop:
  !cenv cx env ann bop e1 e2 es.
    expr_sim_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    expr_sim_pre cenv cx env e1 es /\
    !es'. expr_sim_inv cenv cx env es' /\ source_supply es' ==>
          expr_sim_pre cenv cx env e2 es'
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
  `expr_sim_inv cenv cx env es /\ source_supply es` by
    gvs[expr_sim_pre_def] >>
  `expr_sim_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `is_word_type (expr_type e1) /\ ~is_ArrayT (expr_type e1) /\
   ~is_bytestring_type (expr_type e1) /\
   is_word_type (expr_type e2) /\ ~is_ArrayT (expr_type e2) /\
   ~is_bytestring_type (expr_type e2)` by gvs[word_value_type_word] >>
  imp_res_tac well_typed_expr_type_evaluates >>
  `type_bits (expr_type e1) MOD 8 = 0` by
    (irule byte_widths_expr_type >> gvs[expr_sim_pre_def]) >>
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
  >- (rpt gen_tac >> strip_tac >>
      drule expr_sim_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_sim_pre_lower_value_word_shape >> disch_then drule >> simp[])
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

(* A result of a word type is a value: an ArrayRef is typed by an array
   type, a HashMapRef by NoneTV. *)
Theorem word_type_toplevel_value:
  !t tenv tyv x.
    is_word_type t /\ evaluate_type tenv t = SOME tyv /\
    toplevel_value_typed x tyv ==>
    is_Value x
Proof
  Cases >> rw[is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `x` >> gvs[toplevel_value_typed_def]
QED

(* An expression of a word type evaluates to a value of its type. *)
Theorem expr_sim_pre_word_value:
  !cenv cx env e es tv es'.
    expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) /\
    eval_expr cx e es = (INL tv, es') ==>
    ?v tyv. tv = Value v /\
            evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
            value_has_type tyv v
Proof
  rpt strip_tac >> drule_all expr_sim_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def] >>
  drule_all word_type_toplevel_value >> strip_tac >>
  Cases_on `tv` >> gvs[toplevel_value_typed_def]
QED

(* not: ISZERO, NOT or the flag mask's XOR on the operand
   (exprSimUnop's compile_not_frag); the operand's compile-state shape is
   lower_value_word_shape's. *)
Theorem compile_not_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Not args)
Proof
  rpt strip_tac >>
  `expr_ok cenv (Builtin ann Not args)` suffices_by simp[expr_ok_def] >>
  irule expr_ok_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_not_abs_stack] >>
  rw[expr_sim_ok_def] >>
  `?e1. args = [e1] /\ ann = expr_type e1` by
    (gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  Q.SUBGOAL_THEN `is_bool_type (expr_type e1) \/
                  is_uint256_type (expr_type e1) \/
                  is_bytes32_type (expr_type e1) \/ is_flag_type (expr_type e1)`
    ASSUME_TAC
  >- gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `expr_ok cenv e1` by
    (fs[expr_sim_below_def] >> first_x_assum irule >> simp[]) >>
  `expr_sim_pre cenv cx env e1 es` by
    (drule expr_sim_pre_builtin_arg >> disch_then irule >>
     gvs[expr_sim_pre_def]) >>
  `is_word_type (expr_type e1)` by
    (drule not_type_cases >> rw[] >> gvs[is_word_type_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `expr_type e1`, `Not`,
               `e1`, `expr_type e1`,
               `\x. if expr_type e1 = BaseT BoolT then emit_op ISZERO [x]
                    else compile_invert x (expr_type e1) cenv`, `es`]
    mp_tac compile_unop_sim >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[]
    >- simp[]
    >- (rpt strip_tac >> drule lower_value_not >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_sim_pre_lower_value_word_shape >> disch_then drule >> simp[])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_not])
    >- metis_tac[expr_sim_pre_word_value]
    >- metis_tac[expr_ok_def, expr_sim_ok_def] >>
    rpt strip_tac >> drule_all expr_sim_pre_word_value >> strip_tac >> gvs[] >>
    irule_at Any compile_not_frag >> gvs[] >>
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `expr_sim_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
    simp[expr_sim_pre_def, expr_sim_inv_def] >> rpt strip_tac >>
    first_x_assum irule >>
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  simp[]
QED

Theorem compile_neg_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Neg args)
Proof
  cheat
QED

(* abs: compile_builtin_abs on the operand (exprSimUnop's
   compile_abs_frag); the operand's compile-state shape is
   lower_value_word_shape's. *)
Theorem compile_abs_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Abs args)
Proof
  rpt strip_tac >>
  `expr_ok cenv (Builtin ann Abs args)` suffices_by simp[expr_ok_def] >>
  irule expr_ok_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_not_abs_stack] >>
  rw[expr_sim_ok_def] >>
  `?e1. args = [e1] /\ ann = BaseT (IntT 256) /\
        expr_type e1 = BaseT (IntT 256)` by
    (gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  `expr_ok cenv e1` by
    (fs[expr_sim_below_def] >> first_x_assum irule >> simp[]) >>
  `expr_sim_pre cenv cx env e1 es` by
    (drule expr_sim_pre_builtin_arg >> disch_then irule >>
     gvs[expr_sim_pre_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `BaseT (IntT 256)`, `Abs`,
               `e1`, `ty`, `compile_builtin_abs`, `es`]
    mp_tac compile_unop_sim >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[is_word_type_def]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule lower_value_abs >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_sim_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_abs])
    >- metis_tac[expr_sim_pre_word_value, is_word_type_def]
    >- metis_tac[expr_ok_def, expr_sim_ok_def] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`, `Value v1`, `es1`] mp_tac
      expr_sim_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def, compile_abs_frag]) >>
  simp[]
QED

(* ===== Conditional expression ===== *)

Theorem expr_sim_pre_ifexp:
  !cenv cx env t c a b es.
    expr_sim_pre cenv cx env (IfExp t c a b) es ==>
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    expr_sim_pre cenv cx env c es /\
    !es'. expr_sim_inv cenv cx env es' /\ source_supply es' ==>
          expr_sim_pre cenv cx env a es' /\ expr_sim_pre cenv cx env b es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def] >> gvs[]
QED

(* A ternary of a word type: compile_ifexp_vv_sim (exprSimIfExp), with the
   operands' shape from lower_value_word_shape. *)
Theorem compile_ifexp_word_sim:
  !cenv t c a b.
    expr_sim_below cenv (expr_size (IfExp t c a b)) /\ is_word_type t ==>
    expr_vv_ok cenv (IfExp t c a b)
Proof
  rw[expr_vv_ok_def] >> drule expr_sim_pre_ifexp >> strip_tac >>
  `expr_ok cenv c /\ expr_ok cenv a /\ expr_ok cenv b` by
    (fs[expr_sim_below_def] >> rpt conj_tac >> first_x_assum irule >>
     simp[vyperASTTheory.expr_size_def]) >>
  fs[expr_ok_def] >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  `expr_res_ok res` by
    (qspecl_then [`cenv`, `cx`, `env`, `IfExp t c a b`, `es`, `res`, `es'`]
       mp_tac expr_sim_pre_res_ok >> simp[] >> disch_then irule >>
     rpt strip_tac >>
     drule_all expr_sim_pre_eval >> strip_tac >>
     first_x_assum drule >>
     simp[expr_result_typed_def, expr_runtime_typed_def,
          vyperASTTheory.expr_type_def] >>
     metis_tac[word_type_toplevel_value]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `t`, `c`, `a`, `b`, `es`]
    mp_tac compile_ifexp_vv_sim >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt gen_tac >> strip_tac >>
          drule expr_sim_pre_lower_value_word_shape >> disch_then drule >>
          simp[is_word_type_def])
      >- (rpt gen_tac >> strip_tac >> (* one goal each for e = a and e = b *)
          (`expr_sim_inv cenv cx env es /\ source_supply es` by
             fs[expr_sim_pre_def] >>
           `expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e)` by
             gvs[] >>
           drule expr_sim_pre_lower_value_word_shape >> disch_then drule >>
           simp[]))
      >- metis_tac[expr_sim_ok_def] >>
      rpt gen_tac >> strip_tac >> drule_all expr_sim_pre_eval >> strip_tac >>
      metis_tac[expr_sim_ok_def]) >>
  disch_then irule >> simp[]
QED

(* A ternary of an aggregate type, which supported_pure_expr admits for
   memory arrays, structs and strings (#561).  Cheated: compile_ifexp_vv_sim
   needs the compile-state shape of the branches' lower_value, which for a
   non-word type is #674's compile_expr_shape, and that gives neither
   cs_next_id's growth nor the shape under expr_sim_inv yet.  A ternary over
   storage or transient arrays has an ArrayRef result and a memory copy,
   which vv_holds relates through materialise; its branches' results are
   not expr_res_ok, so it needs their expr_vv_sim and unwrap_value's copy
   rather than their expr_sim (#575). *)
Theorem compile_ifexp_aggregate_sim:
  !cenv t c a b.
    expr_sim_below cenv (expr_size (IfExp t c a b)) /\ ~is_word_type t ==>
    expr_vv_ok cenv (IfExp t c a b)
Proof
  cheat
QED

Theorem compile_ifexp_sim:
  !cenv ann c e1 e2.
    expr_sim_below cenv (expr_size (IfExp ann c e1 e2)) ==>
    expr_vv_ok cenv (IfExp ann c e1 e2)
Proof
  metis_tac[compile_ifexp_word_sim, compile_ifexp_aggregate_sim]
QED
