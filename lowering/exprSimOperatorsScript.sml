(*
 * Expression simulation: the operators (#636, Operators)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the operators and
 * the conditional expression.  The binary operators and the conditional
 * are shared with the body simulation (bodySimExprCases): their case
 * lemmas take the operands' judgments expr_sim_case and expr_vv_case
 * (exprSimHyps), the later operands' where the earlier ones evaluate, as
 * evaluate_ind gives them, and conclude the expression's at the same
 * nocalls flag.
 *
 * TOP-LEVEL:
 *   compile_bop_case         — a binary operator: on operands of
 *                              word_value_type by compile_bop_word_case,
 *                              == and != on address and bytesN by
 *                              compile_bop_bytes_eq_case, the rest by
 *                              compile_bop_rest_case, but for in and not
 *                              in on an array literal
 *   compile_bop_args_case    — the ill-typed ones without two operands
 *   compile_bop_ok           — compile_expr_sim's case: compile_bop_case,
 *                              and compile_bop_in_literal_sim
 *   compile_bop_word_case    — compile_bop_sim (exprSimOps) from the
 *                              operands' simulation and binop_frag_typed
 *   compile_bop_bytes_eq_case — == and != on address and bytesN, whose
 *                              values are BytesV held in their typed words:
 *                              exprSimOps' compile_bop_typed_sim with
 *                              exprSimCompare's compile_compare_bytes_sim
 *   compile_bop_word_sim, compile_bop_bytes_eq_sim — the same at
 *                              expr_sim_ok (the first for stmtSimAugAssign)
 *   expr_body_pre_bop, expr_sim_pre_bop — the operands of a well-typed
 *                              binary operator meet the precondition
 *   compile_not_case, compile_abs_case — not and abs, from the
 *                              operand's exprs_case: exprSimUnop's
 *                              compile_unop_sim with compile_not_frag and
 *                              compile_abs_frag
 *   compile_neg_case         — unary -
 *   compile_ifexp_case       — x if c else y: compile_ifexp_word_case for
 *                              word types, compile_ifexp_aggregate_case
 *                              for the rest
 *   compile_ifexp_sim        — compile_expr_sim's case: compile_ifexp_case
 *
 *   compile_bop_rest_case    — == and != on bytestrings and in and not in
 *                              on arrays (#569), Operators row 6: on arrays
 *                              of words by exprSimBopRestWord, the rest by
 *                              exprSimBopHeld (held for #742)
 *   compile_bop_in_literal_sim — the same row for in and not in on an
 *                              array literal: of words by
 *                              exprSimBopInLiteralWord, the rest by
 *                              exprSimBopHeld (held for #742)
 *
 * Row 9, ternaries, is proved: word ternaries by compile_ifexp_word_case,
 * aggregate ones by compile_ifexp_aggregate_case, and with them row 8's
 * and/or chains (#556), which the frontend desugars to nested IfExps of
 * type bool (translate_boolop).  Bop And/Or are the bitwise & and |.
 *
 * Compile-side facts:
 *   lower_value_word_shape   — lowering a well-typed word expression only
 *                              appends, hands out its variables, and
 *                              returns a variable it handed out or a literal
 *   compile_binop_shape      — compile_binop only appends
 * compile_bop_word_case rests on these two and on binop_frag_typed, and
 * compile_ifexp_word_case, compile_not_case, compile_abs_case and
 * exprSimConvert's compile_convert_word_case on lower_value_word_shape.
 *
 * Helpers: expr_body_pre_lower_value_word_shape, expr_body_pre_word_value,
 *   expr_body_pre_word_type_result, expr_body_pre_ifexp and their
 *   expr_sim_pre corollaries.
 *)

Theory exprSimOperators
Ancestors
  exprSimBopRestWord exprSimBopInLiteralWord exprSimBopHeld
  exprSimUnopCompose
  exprSimBopTyped
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimIfExp exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering exprLoweringProps compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation

(* ===== Compile-side facts ===== *)

(* The typing hypotheses keep a pointer from cenv out of the value.
   unwrap_value loads only a word, and some conversions return their
   operand: for an ill-typed e, convert(s, uint256) with s a struct lowers
   to the pointer to s (ConvIdentity); for a local of the ill-formed type
   bytes40, which the Name typing rule admits, convert(x, bytes32) lowers
   to the pointer to x (ConvBytesMToBytesM). *)
Theorem compile_binop_shape:
  !bop x y ty bl el sa op sb.
    compile_binop bop x y ty bl el sa = (op, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule exprLoweringPropsTheory.compile_binop_grows >> simp[]
QED

(* lower_value_word_shape for an operand that meets expr_body_pre, which
   carries both typing hypotheses. *)
Theorem expr_sim_pre_lower_value_word_shape:
  !cenv cx env e es ty sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  metis_tac[expr_body_pre_lower_value_word_shape, expr_sim_pre_body_pre]
QED

(* ===== Binary operators ===== *)

(* Forced success has the expression's evaluated type, including place reads. *)
Theorem expr_sim_pre_word_value:
  !cenv cx env e es v es'.
    expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    ?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
          value_has_type tyv v
Proof
  metis_tac[expr_body_pre_word_value, expr_sim_pre_body_pre]
QED

Theorem well_typed_binop_word_result:
  !ann bop t1 t2.
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 ==>
    is_word_type ann
Proof
  rpt strip_tac >> drule word_value_type_word >> strip_tac >>
  Cases_on `bop` >> gvs[well_typed_binop_def, is_word_type_def]
QED

(* A well-typed binary operator has two operands. *)
Theorem expr_body_pre_bop_args:
  !cenv cx env ann bop args es.
    expr_body_pre cenv cx env (Builtin ann (Bop bop) args) es ==>
    ?e1 e2. args = [e1; e2]
Proof
  rw[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[listTheory.LENGTH_EQ_NUM_compute]
QED

Theorem expr_body_pre_bop:
  !cenv cx env ann bop e1 e2 es.
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    expr_body_pre cenv cx env e1 es /\
    !es'. expr_sim_inv cenv cx env es' ==> expr_body_pre cenv cx env e2 es'
Proof
  rpt gen_tac >>
  simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_evm_run_root_def,
       listTheory.EVERY_APPEND] >>
  strip_tac >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
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

(* The operands' internal calls: none if the operator has none. *)
Theorem int_calls_bop_operands[local]:
  !nocalls ann bop e1 e2.
    (nocalls ==> int_calls_expr (Builtin ann (Bop bop) [e1; e2]) = []) ==>
    (nocalls ==> int_calls_expr e1 = []) /\
    (nocalls ==> int_calls_expr e2 = [])
Proof
  Cases >> simp[int_calls_expr_def]
QED

(* Two operands of word_value_type: compile_bop_sim (exprSimOps), the
   operands' simulation from their judgments, e2's where e1 evaluates and
   is read, and binop_frag_typed. *)
Theorem compile_bop_word_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    expr_sim_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2) /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >> simp[Once expr_sim_case_def] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_operands >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  drule int_calls_bop_operands >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `is_word_type (expr_type e1) /\ ~is_ArrayT (expr_type e1) /\
   ~is_bytestring_type (expr_type e1) /\
   is_word_type (expr_type e2) /\ ~is_ArrayT (expr_type e2) /\
   ~is_bytestring_type (expr_type e2)` by gvs[word_value_type_word] >>
  imp_res_tac expr_body_pre_type_evaluates >>
  `type_bits (expr_type e1) MOD 8 = 0` by
    (irule byte_widths_expr_type >> gvs[expr_body_pre_def]) >>
  `is_word_type ann` by (drule_all well_typed_binop_word_result >> simp[]) >>
  irule compile_bop_sim >> rpt conj_tac
  >~ [`binop_frag`]
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`,
                   `INL v1`, `es1`] mp_tac expr_body_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v1` mp_tac) >> simp[] >> strip_tac >>
      rename1 `value_has_type tv1 v1` >>
      `expr_body_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      `expr_sim_case nocalls ctx func cenv cx e2` by
        (drule eval_expr_read_INL >> strip_tac >> first_x_assum irule >>
         metis_tac[]) >>
      conj_tac >- gvs[] >>
      conj_tac
      >- (irule expr_sim_case_apply >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1 with gas_obs := gs2`,
                   `INL v2`, `es2`] mp_tac expr_body_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v2` mp_tac) >> simp[] >>
      strip_tac >> rename1 `value_has_type tv2 v2` >> simp[] >>
      drule eval_expr_read_INL >> strip_tac >>
      rev_drule eval_expr_read_INL >> strip_tac >>
      `(!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
       (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n)` by
        metis_tac[eval_expr_int_literal_agrees] >>
      `(bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i)` by
        (strip_tac >> irule eval_expr_shift_amount >> metis_tac[]) >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `e1`, `e2`,
                   `v1`, `v2`, `es2`, `tv1`, `tv2`] mp_tac binop_frag_typed >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`expr_sim`]
  >- (irule expr_sim_case_apply >> metis_tac[]) >>
  gvs[]
QED

Theorem compile_bop_word_sim:
  !cenv ann bop e1 e2.
    expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) [e1; e2])
Proof
  simp[expr_sim_ok_case] >> rpt strip_tac >> irule compile_bop_word_case >>
  simp[]
QED

(* ===== Equality on address and bytesN ===== *)

(* The result of an operand of a word type: an address or a bytesN one
   is no word_value_type, so expr_body_pre_word_result does not cover it. *)
Theorem expr_body_pre_word_type_result:
  !cenv cx env e es res es'.
    expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==>
        ?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
              value_has_type tyv v
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all expr_body_pre_eval >> simp[]) >>
  rw[] >> drule_all expr_body_pre_word_value >> simp[]
QED

Theorem expr_sim_pre_word_type_result:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ is_word_type (expr_type e) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\
    !v. res = INL v ==>
        ?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
              value_has_type tyv v
Proof
  metis_tac[expr_body_pre_word_type_result, expr_sim_pre_body_pre]
QED

(* == and != on two address or two bytesN operands: compile_bop_typed_sim
   (exprSimOps), the operands held in their typed words, with
   compile_compare_bytes_sim (exprSimCompare) for the EQ on them. *)
Theorem compile_bop_bytes_eq_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    expr_sim_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2) /\
    (bop = Eq \/ bop = NotEq) /\
    (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m))) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  (* one goal for the four cases: they are split only where it matters *)
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp[Once expr_sim_case_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  drule int_calls_bop_operands >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `expr_type e2 = expr_type e1 /\ ann = BaseT BoolT` by
    (qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
     gvs[well_typed_binop_def]) >>
  `?ot. evaluate_type (get_tenv cx) (expr_type e1) = SOME ot` by
    (qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`] mp_tac
       expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
   ~is_bytestring_type (expr_type e1) /\ ~is_ArrayT (expr_type e2)` by
    (qpat_x_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
     gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION,
         is_word_type_def, is_bytestring_type_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e2) = SOME ot` by gvs[] >>
  irule compile_bop_typed_sim >> rpt conj_tac
  >~ [`binop_frag_words`]
  >- (qexistsl_tac [`ot`, `ot`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`,
                   `INL v1`, `es1`] mp_tac expr_body_pre_word_type_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v1` mp_tac) >> simp[] >> strip_tac >>
      `expr_body_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      `expr_sim_case nocalls ctx func cenv cx e2` by
        (drule eval_expr_read_INL >> strip_tac >> first_x_assum irule >>
         metis_tac[]) >>
      conj_tac
      >- (irule expr_sim_case_apply >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1 with gas_obs := gs2`,
                   `INL v2`, `es2`] mp_tac expr_body_pre_word_type_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v2` mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
      gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      irule compile_compare_bytes_sim >> fs[value_has_type_def])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`expr_sim`]
  >- (irule expr_sim_case_apply >> metis_tac[]) >>
  gvs[is_word_type_def]
QED

Theorem compile_bop_bytes_eq_sim:
  !cenv ann bop e1 e2.
    expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2 /\ (bop = Eq \/ bop = NotEq) /\
    (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m))) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) [e1; e2])
Proof
  simp[expr_sim_ok_case] >> rpt strip_tac >> irule compile_bop_bytes_eq_case >>
  simp[]
QED

(* The rest of the binary operators whose operands are not both
   of word_value_type: == and != on bytestrings, which compare the
   keccak256 hashes of the operands' bytes, and in and not in on arrays
   (#569), but for in and not in on an array literal
   (compile_bop_in_literal_sim).  Bytestring equality and membership in
   an array of non-words are held for #742 (exprSimBopHeld).  Nothing else is left: the other
   operators take operands of word_value_type (well_typed_binop), and a
   bytesN wider than 32 bytes does not evaluate
   (expr_body_pre_type_evaluates). *)
Theorem compile_bop_rest_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    expr_sim_case nocalls ctx func cenv cx e1 /\
    expr_vv_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2 /\
     expr_vv_case nocalls ctx func cenv cx e2) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >>
  Cases_on `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)`
  >- (MATCH_MP_TAC compile_bop_bytestring_eqne_case >> first_assum ACCEPT_TAC) >>
  Cases_on `(bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)`
  >- (MATCH_MP_TAC compile_bop_nonword_membership_case >>
      first_assum ACCEPT_TAC) >>
  MATCH_MP_TAC compile_bop_rest_word_case >> conj_tac >> first_assum ACCEPT_TAC
QED

(* In and not in on an array literal (#569), which the lowering
   unrolls to a comparison with each element (compile_multi_exprs), so it
   takes the elements' judgments, not the array's.  An array literal of
   non-words is held for #742 (exprSimBopHeld).  The body simulation,
   whose operand judgments are the array's, leaves this case as
   bodySimExprCases' body_bop_in_literal_case. *)
Theorem compile_bop_in_literal_sim:
  !cenv ann bop e1 a t n elems.
    expr_sim_below cenv
      (list_size expr_size [e1; Builtin a (MakeArray t n) elems]) /\
    (bop = In \/ bop = NotIn) ==>
    expr_ok cenv (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt gen_tac >> Cases_on `is_word_type (expr_type e1)`
  >- (MATCH_MP_TAC compile_bop_in_literal_word_sim >> first_assum ACCEPT_TAC) >>
  MATCH_MP_TAC compile_bop_in_literal_nonword_sim >> first_assum ACCEPT_TAC
QED

(* ===== All binary operators ===== *)

Theorem stack_value_pair_exists[local]:
  ?t op sb. (StackValue a x, y) = (StackValue t op, sb)
Proof
  simp[]
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
  (* reduce the case on the builtin top-down, then close each of the ~100
     goals, a StackValue pair, by rewriting rather than a full simp *)
  rename1 `Builtin _ bi _` >> Cases_on `bi` >>
  ONCE_REWRITE_TAC [vyperASTTheory.builtin_case_def] >>
  rewrite_tac[stack_value_pair_exists] >> simp[]
QED

(* A binary operator, from its operands' judgments, e2's where e1
   evaluates and is read, as evaluate_ind gives them: on operands of
   word_value_type by compile_bop_word_case, == and != on address and
   bytesN by compile_bop_bytes_eq_case, the rest by compile_bop_rest_case.
   It leaves out in and not in on an array literal
   (compile_bop_in_literal_sim). *)
Theorem compile_bop_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    expr_sim_case nocalls ctx func cenv cx e1 /\
    expr_vv_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2 /\
     expr_vv_case nocalls ctx func cenv cx e2) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2]) /\
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])` by
    (Cases_on `word_value_type (expr_type e1) /\
               word_value_type (expr_type e2)`
     >- (irule compile_bop_word_case >> simp[] >> rpt strip_tac >>
         metis_tac[]) >>
     Cases_on `(bop = Eq \/ bop = NotEq) /\
               (expr_type e1 = BaseT AddressT \/
                ?m. expr_type e1 = BaseT (BytesT (Fixed m)))`
     >- (irule compile_bop_bytes_eq_case >> simp[] >> rpt strip_tac >>
         metis_tac[]) >>
     irule compile_bop_rest_case >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> irule expr_vv_case_stack >> simp[compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value]
QED

(* An ill-typed binary operator, without two operands, meets no
   expr_body_pre. *)
Theorem compile_bop_args_case:
  !nocalls ctx func cenv cx ann bop args.
    (!e1 e2. args <> [e1; e2]) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) args) /\
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Bop bop) args)
Proof
  rw[expr_sim_case_def, expr_vv_case_def] >>
  drule expr_body_pre_bop_args >> strip_tac >> gvs[]
QED

Theorem compile_bop_ok:
  !cenv ann bop args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_ok cenv (Builtin ann (Bop bop) args)
Proof
  rpt strip_tac >> simp[expr_ok_case] >> rpt gen_tac >>
  Cases_on `?e1 e2. args = [e1; e2]`
  >- (pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      Cases_on `(bop = In \/ bop = NotIn) /\
                ?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- (qpat_x_assum `_ /\ ?a t n elems. _`
            (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
          rpt BasicProvers.VAR_EQ_TAC >>
          `expr_ok cenv (Builtin ann (Bop bop)
                           [e1; Builtin a (MakeArray t n) elems])` by
            (irule compile_bop_in_literal_sim >> rpt conj_tac >>
             first_assum ACCEPT_TAC) >>
          fs[expr_ok_case]) >>
      `expr_ok cenv e1 /\ expr_ok cenv e2` by
        metis_tac[expr_sim_below_mem, listTheory.MEM] >>
      gvs[expr_ok_case] >> irule compile_bop_case >> simp[]) >>
  irule compile_bop_args_case >> gvs[]
QED

(* ===== Unary operators ===== *)

(* A unary builtin's operand: its expr_sim at the builtin's state, from
   the operand's exprs_case. *)
Theorem unop_operand_sim:
  !nocalls ctx func cenv cx env ann bi e1 ty1 es.
    exprs_case nocalls ctx func cenv cx [e1] /\
    expr_body_pre cenv cx env (Builtin ann bi [e1]) es /\
    (nocalls ==> int_calls_expr (Builtin ann bi [e1]) = []) ==>
    expr_body_pre cenv cx env e1 es /\ expr_sim ctx func cenv cx ty1 e1 es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e1 es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def] >> disj1_tac >> rpt strip_tac >>
     gvs[well_typed_expr_def, well_typed_builtin_app_def]) >>
  gvs[exprs_case_def] >> irule expr_sim_case_apply >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexists `nocalls` >> simp[] >>
  metis_tac[int_calls_builtin_arg, listTheory.MEM]
QED

(* not: ISZERO, NOT or the flag mask's XOR on the operand
   (exprSimUnop's compile_not_frag); the operand's compile-state shape is
   lower_value_word_shape's. *)
Theorem compile_not_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Not args)
Proof
  rpt strip_tac >> irule expr_vv_case_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_not_abs_stack] >>
  rw[expr_sim_case_def] >>
  `?e1. args = [e1] /\ ann = expr_type e1` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  Q.SUBGOAL_THEN `is_bool_type (expr_type e1) \/
                  is_uint256_type (expr_type e1) \/
                  is_bytes32_type (expr_type e1) \/ is_flag_type (expr_type e1)`
    ASSUME_TAC
  >- gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `expr_body_pre cenv cx env e1 es /\ expr_sim ctx func cenv cx ty e1 es` by
    metis_tac[unop_operand_sim] >>
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
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[]
    >- simp[]
    >- (rpt strip_tac >> drule lower_value_not >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_not])
    >- metis_tac[unop_operand_sim] >>
    rpt strip_tac >>
    `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
    drule_all expr_body_pre_word_value >> strip_tac >> gvs[] >>
    irule_at Any compile_not_frag >> gvs[] >>
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
    simp[expr_body_pre_def, expr_sim_inv_def] >> rpt strip_tac >>
    first_x_assum irule >>
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  simp[]
QED

Theorem expr_body_pre_neg:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann Neg args) es ==>
    ?e1. args = [e1] /\ ann = expr_type e1 /\
      is_numeric_type (expr_type e1) /\ ~is_uint_type (expr_type e1) /\
      expr_body_pre cenv cx env e1 es
Proof
  rpt strip_tac >>
  `?e1. args = [e1] /\ ann = expr_type e1 /\
        is_numeric_type (expr_type e1) /\ ~is_uint_type (expr_type e1)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  drule expr_body_pre_builtin_arg >> disch_then irule >>
  gvs[expr_body_pre_def]
QED

Theorem compile_neg_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Neg args)
Proof
  rpt strip_tac >> irule expr_vv_case_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_neg_stack] >>
  rw[expr_sim_case_def] >>
  drule expr_body_pre_neg >> strip_tac >> gvs[] >> (
  `is_word_type (expr_type e1)` by
    (Cases_on `expr_type e1` >>
     gvs[is_numeric_type_def, is_int_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def]) >>
  irule compile_unop_sim >> simp[builtin_args_length_ok_def, is_word_type_def] >>
  qexistsl [`\x. compile_neg x (expr_type e1)`, `expr_type e1`] >>
  rpt conj_tac
  >~ [`unop_frag`]
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
      drule_all expr_body_pre_word_value >> strip_tac >> gvs[] >>
      irule_at Any compile_neg_frag >>
      gvs[is_numeric_type_def, is_uint_type_def])
  >~ [`expr_sim`]
  >- metis_tac[unop_operand_sim]
  >~ [`Builtin`]
  >- (rpt strip_tac >> drule lower_value_neg >> simp[])
  >~ [`compile_neg`]
  >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
      simp[CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg]) >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
QED

(* abs: compile_builtin_abs on the operand (exprSimUnop's
   compile_abs_frag); the operand's compile-state shape is
   lower_value_word_shape's. *)
Theorem compile_abs_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Abs args)
Proof
  rpt strip_tac >> irule expr_vv_case_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_not_abs_stack] >>
  rw[expr_sim_case_def] >>
  `?e1. args = [e1] /\ ann = BaseT (IntT 256) /\
        expr_type e1 = BaseT (IntT 256)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  `expr_body_pre cenv cx env e1 es /\ expr_sim ctx func cenv cx ty e1 es` by
    metis_tac[unop_operand_sim] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `BaseT (IntT 256)`, `Abs`,
               `e1`, `ty`, `compile_builtin_abs`, `es`]
    mp_tac compile_unop_sim >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[is_word_type_def]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule lower_value_abs >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_abs])
    >- simp[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`, `v1`, `es1`] mp_tac
      expr_body_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def, compile_abs_frag]) >>
  simp[]
QED

(* ===== Conditional expression ===== *)

Theorem expr_body_pre_ifexp:
  !cenv cx env t c a b es.
    expr_body_pre cenv cx env (IfExp t c a b) es ==>
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    expr_body_pre cenv cx env c es /\
    !es'. expr_sim_inv cenv cx env es' ==>
          expr_body_pre cenv cx env a es' /\ expr_body_pre cenv cx env b es'
Proof
  rpt gen_tac >>
  simp[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_evm_run_root_def,
       listTheory.EVERY_APPEND] >>
  strip_tac >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right]
QED

Theorem expr_sim_pre_ifexp:
  !cenv cx env t c a b es.
    expr_sim_pre cenv cx env (IfExp t c a b) es ==>
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    expr_sim_pre cenv cx env c es /\
    !es'. expr_sim_inv cenv cx env es' ==>
          expr_sim_pre cenv cx env a es' /\ expr_sim_pre cenv cx env b es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.supported_expr_exists_def,
     byte_widths_expr_def, alloc_limits_expr_def] >> gvs[] >> metis_tac[]
QED

(* A conditional retains a place only for a memory aggregate. *)
Theorem word_type_conditional_result_value:
  !t env cx st source x.
    is_word_type t /\ eval_result_typed (env,cx,st) x (Type t) /\
    conditional_result cx source st = (INL x,st) ==>
    is_Value x
Proof
  rpt strip_tac >> Cases_on `x` >> gvs[] >>
  Cases_on `source` >>
  gvs[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `if keep then _ else _` >>
  Cases_on `keep` >> gvs[bind_def, return_def, AllCaseEqs()] >>
  gvs[eval_result_typed_def, runtime_place_typed_def] >>
  imp_res_tac vyperStateTheory.place_type_value_state >> gvs[] >>
  (Cases_on `t` >> gvs[is_word_type_def])
  >>~- ([`is_word_type (BaseT bt)`],
         (Cases_on `bt` >> gvs[is_word_type_def])
         >>~- ([`is_word_type (BaseT (BytesT bd))`],
                Cases_on `bd` >> gvs[is_word_type_def] >>
                gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
         gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]
QED

Theorem expr_body_pre_ifexp_word_readable:
  !cenv cx env t c a b es res es'.
    expr_body_pre cenv cx env (IfExp t c a b) es /\ is_word_type t /\
    eval_expr cx (IfExp t c a b) es = (res,es') ==>
    expr_read_res_ok cx es' res
Proof
  rpt strip_tac >> drule_all expr_body_pre_eval_result >> strip_tac >>
  Cases_on `res`
  >- (rename1 `eval_expr _ _ _ = (INL r,_)` >>
      `is_Value r` by
        (qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
         simp[NoAsms, Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
         strip_tac >> imp_res_tac read_result_state >>
         imp_res_tac vyperStatePreservationTheory.conditional_result_state >> gvs[] >>
         gvs[expr_type_def] >>
         drule_all word_type_conditional_result_value >> simp[]) >>
      Cases_on `r` >> gvs[expr_read_res_ok_def, read_result_def, return_def]) >>
  drule_all expr_body_pre_vv_res_ok >>
  simp[expr_vv_res_ok_def, expr_read_res_ok_def, expr_res_ok_def]
QED

(* The operands' internal calls: none if the conditional has none. *)
Theorem int_calls_ifexp_operands[local]:
  !nocalls t c a b.
    (nocalls ==> int_calls_expr (IfExp t c a b) = []) ==>
    (nocalls ==> int_calls_expr c = []) /\
    (nocalls ==> int_calls_expr a = []) /\
    (nocalls ==> int_calls_expr b = [])
Proof
  Cases >> simp[int_calls_expr_def]
QED

(* A ternary of a word type: compile_ifexp_word_vv_sim (exprSimIfExp),
   with the condition's simulation from its judgment, both judgments of
   the branches where the condition evaluates, and their shape from
   lower_value_word_shape. *)
Theorem compile_ifexp_word_case:
  !nocalls ctx func cenv cx t c a b.
    is_word_type t /\ expr_sim_case nocalls ctx func cenv cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     expr_sim_case nocalls ctx func cenv cx a /\
     expr_vv_case nocalls ctx func cenv cx a /\
     expr_sim_case nocalls ctx func cenv cx b /\
     expr_vv_case nocalls ctx func cenv cx b) ==>
    expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >> simp[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_ifexp >> strip_tac >>
  drule int_calls_ifexp_operands >> strip_tac >>
  irule compile_ifexp_word_vv_sim >> simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
      simp[is_word_type_def])
  >- (rpt gen_tac >> strip_tac >>
      (`expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
       `expr_body_pre cenv cx env e es /\ is_word_type (expr_type e)` by
         gvs[] >>
       drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
       simp[]))
  >~ [`expr_sim _ _ _ _ (BaseT BoolT) c es`]
  >- (irule expr_sim_case_apply >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env c (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  drule eval_expr_read_INL >> strip_tac >>
  `expr_sim_case nocalls ctx func cenv cx a /\
   expr_vv_case nocalls ctx func cenv cx a /\
   expr_sim_case nocalls ctx func cenv cx b /\
   expr_vv_case nocalls ctx func cenv cx b` by
    (qpat_x_assum `(?s tv s'. _) ==> _` mp_tac >>
     impl_tac >- metis_tac[] >> simp[]) >>
  rpt conj_tac
  >- (irule expr_sim_case_apply >> metis_tac[])
  >- (irule expr_sim_case_apply >> metis_tac[])
  >- (fs[expr_vv_case_def] >> metis_tac[]) >>
  fs[expr_vv_case_def] >> metis_tac[]
QED

(* A ternary of an aggregate type, which supported_pure_expr admits for
   memory arrays, structs and strings (#561): compile_ifexp_vv_sim
   (exprSimIfExp), as for word types, with the branches' shape from
   compile_expr_grows.  A ternary over storage or transient arrays copies
   its value to memory. *)
Theorem compile_ifexp_aggregate_case:
  !nocalls ctx func cenv cx t c a b.
    ~is_word_type t /\
    (~nocalls ==>
     !e. (e = a \/ e = b) ==>
         (int_calls_expr e = [] \/
          same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
         post_value_type cenv e = expr_type e) /\
    expr_sim_case nocalls ctx func cenv cx c /\
    expr_vv_case nocalls ctx func cenv cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     expr_sim_case nocalls ctx func cenv cx a /\
     expr_vv_case nocalls ctx func cenv cx a /\
     expr_sim_case nocalls ctx func cenv cx b /\
     expr_vv_case nocalls ctx func cenv cx b) ==>
    expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >> simp[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_ifexp >> strip_tac >>
  drule int_calls_ifexp_operands >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `t`, `c`, `a`, `b`, `es`]
    mp_tac compile_ifexp_vv_sim >>
  `!e. (e = a \/ e = b) ==> post_value_type cenv e = expr_type e` by
    (rpt strip_tac >> Cases_on `nocalls` >> gvs[] >>
     metis_tac[post_value_type_no_calls]) >>
  pop_assum (fn th => disch_then (mp_tac o REWRITE_RULE [EQT_INTRO th])) >>
  impl_tac
  >- (simp[] >> rpt conj_tac
      >- (rpt gen_tac >> disch_tac >>
          `expr_body_pre cenv cx env e es` by
            (`expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
             metis_tac[]) >>
          qpat_assum `expr_body_pre _ _ _ e _`
            (mp_then Any mp_tac ifexp_body_pre_lowered_type_compatible) >>
          impl_tac >- (Cases_on `nocalls` >> metis_tac[]) >>
          rpt strip_tac >> simp[])
      >- (rpt gen_tac >> disch_tac >>
          qspecl_then [`cenv`, `cx`, `env`, `IfExp t c a b`]
            mp_tac expr_body_pre_copy_ok >>
          simp[vyperASTTheory.expr_type_def] >>
          disch_then (qspec_then `es` mp_tac) >> simp[])
      >- metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows]
      >- metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows]
      >- (irule expr_sim_case_apply >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env c (es with gas_obs := gs)` by simp[] >>
      drule_all expr_body_pre_eval >> strip_tac >>
      drule eval_expr_read_INL >> strip_tac >>
      `expr_sim_case nocalls ctx func cenv cx a /\
       expr_vv_case nocalls ctx func cenv cx a /\
       expr_sim_case nocalls ctx func cenv cx b /\
       expr_vv_case nocalls ctx func cenv cx b` by
        (qpat_x_assum `(?s tv s'. _) ==> _` mp_tac >>
         impl_tac >- metis_tac[] >> simp[]) >>
      conj_tac >- (irule expr_sim_case_apply >> metis_tac[]) >>
      conj_tac >- (irule expr_sim_case_apply >> metis_tac[]) >>
      conj_tac >- (fs[expr_vv_case_def] >> metis_tac[]) >>
      conj_tac >- (fs[expr_vv_case_def] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      `expr_body_pre cenv cx env a es1 /\ expr_body_pre cenv cx env b es1` by
        metis_tac[] >>
      metis_tac[ifexp_body_pre_read_typed, expr_body_pre_gas_obs]) >>
  simp[]
QED

(* x if c else y, from its operands' judgments, the branches' where the
   condition evaluates, as evaluate_ind gives them:
   compile_ifexp_word_case for word types, compile_ifexp_aggregate_case
   for the rest. *)
Theorem compile_ifexp_case:
  !nocalls ctx func cenv cx t c a b.
    (~nocalls ==>
     !e. (e = a \/ e = b) ==>
         (int_calls_expr e = [] \/
          same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
         post_value_type cenv e = expr_type e) /\
    expr_sim_case nocalls ctx func cenv cx c /\
    expr_vv_case nocalls ctx func cenv cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     expr_sim_case nocalls ctx func cenv cx a /\
     expr_vv_case nocalls ctx func cenv cx a /\
     expr_sim_case nocalls ctx func cenv cx b /\
     expr_vv_case nocalls ctx func cenv cx b) ==>
    expr_sim_case nocalls ctx func cenv cx (IfExp t c a b) /\
    expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)` by
    (Cases_on `is_word_type t`
     >- (irule compile_ifexp_word_case >> simp[] >> rpt strip_tac >>
         metis_tac[]) >>
     irule compile_ifexp_aggregate_case >> rpt conj_tac >>
     first_assum ACCEPT_TAC) >>
  simp[expr_sim_case_of_vv]
QED

Theorem compile_ifexp_sim:
  !cenv ann c e1 e2.
    expr_sim_below cenv (expr_size (IfExp ann c e1 e2)) ==>
    expr_vv_ok cenv (IfExp ann c e1 e2)
Proof
  rpt strip_tac >>
  `expr_ok cenv c /\ expr_ok cenv e1 /\ expr_ok cenv e2` by
    (fs[expr_sim_below_def] >> rpt conj_tac >> first_x_assum irule >>
     simp[vyperASTTheory.expr_size_def]) >>
  gvs[expr_ok_case, expr_vv_ok_case] >> rpt gen_tac >>
  qspecl_then [`T`, `ctx`, `func`, `cenv`, `cx`, `ann`, `c`, `e1`, `e2`]
    mp_tac compile_ifexp_case >>
  simp[]
QED
