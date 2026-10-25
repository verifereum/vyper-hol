(*
 * Expression simulation: aggregates and type builtins (#636, Aggregates
 * and type builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for struct and array
 * literals and the type builtins but extract32.  Cheated, for the later
 * #636 PRs, but for max_value, min_value, epsilon and the conversions
 * exprSimConvert proves (which rest on the cheated
 * lower_value_word_shape).
 *
 * TOP-LEVEL:
 *   compile_struct_lit_sim, compile_make_array_sim — StructLit, MakeArray
 *                           (lists and tuples), row 1
 *   compile_empty_sim     — empty(T), row 2
 *   compile_bound_builtin_case_sim — max_value, min_value and epsilon of
 *                           a numeric type (row 2): a Lit of the bound.
 *                           compile_max_value_sim, compile_min_value_sim
 *                           and compile_epsilon_sim follow from it
 *   compile_convert_sim   — convert, row 3: compile_convert_word_sim
 *                           (exprSimConvert) between integer types, from
 *                           bool to an integer and from an integer to
 *                           bool; compile_convert_other_sim for the rest
 *                           (#548)
 *   compile_abi_encode_sim, compile_abi_decode_sim — abi_encode (#551),
 *                           abi_decode with its validation aborts, row 4
 *
 * The StructLit case takes the field layout from the literal's own struct,
 * whatever the caller's ty (compile_expr_struct_lit_ty).  That layout
 * comes from ce_struct_fields, so compile_struct_lit_sim still needs
 * expr_sim_inv's struct-metadata clause (exprSimHyps, "Not here yet").
 *
 * The elements of a struct or array literal are lowered as
 * cfn ...; ADD ...; unwrap_value, and an element that is a storage or
 * transient array evaluates to an ArrayRef: these lemmas use the induction
 * hypothesis's expr_vv_ok of each element (expr_sim_below_mem), not
 * expr_sim_ok.  Composing the elements needs the operand composition of
 * #636's Infrastructure (a value an earlier operand left in memory survives
 * a later operand's fragment).
 *)

Theory exprSimAggregates
Ancestors
  list exprSim exprSimHyps exprSimConvert exprLowering compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperTypeSystem fragExec venomState

Theorem compile_struct_lit_sim:
  !cenv ann nsid fields.
    expr_sim_below cenv (expr_size (StructLit ann nsid fields)) ==>
    expr_vv_ok cenv (StructLit ann nsid fields)
Proof
  cheat
QED

Theorem compile_make_array_sim:
  !cenv ann topt bnd args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (MakeArray topt bnd) args)
Proof
  cheat
QED

Theorem compile_empty_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Empty t args)
Proof
  cheat
QED

(* ===== max_value, min_value, epsilon ===== *)

Theorem eval_expr_bound_builtin:
  !cx ann tb t args es res es'.
    eval_expr cx (TypeBuiltin ann tb t args) es = (res, es') /\
    expr_res_ok res /\ MEM tb [MaxValue; MinValue; Epsilon] ==>
    es' = es /\ args = [] /\
    ?v. res = INL (Value v) /\ evaluate_type_builtin cx tb t [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  `!n. type_builtin_args_length_ok tb n <=> n = 0` by
    (Cases_on `tb` >> gvs[type_builtin_args_length_ok_def]) >>
  `!y. evaluate_type_builtin cx tb t [] = INR y ==> ?m. y = TypeError m` by
    (Cases_on `tb` >> gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
     Cases_on `t` >> gvs[evaluate_max_value_def, evaluate_min_value_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[evaluate_max_value_def, evaluate_min_value_def, AllCaseEqs()]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `args` >> simp[raise_def] >>
  simp[Once evaluate_def, return_def] >>
  Cases_on `evaluate_type_builtin cx tb t []` >>
  simp[return_def, raise_def] >> rw[] >> gvs[expr_res_ok_def]
QED

(* max_value, min_value and epsilon of a numeric type: a Lit of the bound,
   no code. *)
Theorem compile_bound_builtin_word_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_sim_ok cenv (TypeBuiltin ann tb t args)
Proof
  rw[expr_sim_ok_def, expr_sim_def] >>
  drule eval_expr_bound_builtin >> disch_then drule >> simp[] >>
  strip_tac >> gvs[] >>
  `ann = t /\ is_numeric_type t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT` by
    (Cases_on `t` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  gvs[] >>
  gvs[evaluate_type_builtin_def, evaluate_max_value_def,
      evaluate_min_value_def, AllCaseEqs()] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def,
      type_bounds_def, type_bits_def, is_signed_type_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  simp[integerTheory.INT_SUB] >>
  rw[vyperValueTheory.evaluate_type_def] >>
  gvs[AllCaseEqs(), typed_val_to_w256_def, val_to_w256_def,
      integer_wordTheory.i2w_def]
QED

Theorem compile_bound_builtin_case_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_ok cenv (TypeBuiltin ann tb t args)
Proof
  rpt strip_tac >> irule expr_ok_stack >> rpt conj_tac
  >~ [`eval_expr`] >- metis_tac[eval_expr_type_builtin_value]
  >~ [`expr_sim_ok`]
  >- (irule compile_bound_builtin_word_sim >> first_assum ACCEPT_TAC) >>
  Cases_on `tb` >> gvs[] >> rpt gen_tac >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def] >>
  Cases_on `type_bounds t` >> simp[]
QED

Theorem compile_max_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann MaxValue t args)
Proof
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def, listTheory.MEM]
QED

Theorem compile_min_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann MinValue t args)
Proof
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def, listTheory.MEM]
QED

Theorem compile_epsilon_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Epsilon t args)
Proof
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def, listTheory.MEM]
QED

(* The conversions exprSimConvert does not cover: those to or from
   decimal, address, bytesM, bytestrings and flags.  Cheated: for several
   of them the checker, the lowering and the semantics disagree (#548). *)
Theorem compile_convert_other_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) /\
    ~(?e1. args = [e1] /\ int_convert_pair (expr_type e1) t) ==>
    expr_vv_ok cenv (TypeBuiltin ann Convert t args)
Proof
  cheat
QED

Theorem compile_convert_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Convert t args)
Proof
  rpt strip_tac >>
  Cases_on `?e1. args = [e1] /\ int_convert_pair (expr_type e1) t`
  >- (gvs[] >> irule compile_convert_word_sim >> simp[]) >>
  irule compile_convert_other_sim >> metis_tac[]
QED

Theorem compile_abi_encode_sim:
  !cenv ann ensure mid t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann (AbiEncode ensure mid) t args)
Proof
  cheat
QED

Theorem compile_abi_decode_sim:
  !cenv ann unwrap t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann (AbiDecode unwrap) t args)
Proof
  cheat
QED
