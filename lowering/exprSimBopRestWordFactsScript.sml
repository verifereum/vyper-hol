(* Typing and dispatch boundaries for nonliteral word-array membership. *)
Theory exprSimBopRestWordFacts
Ancestors
  exprSimHypsDefs vyperTypeSystem compileEnv exprLowering exprBopSimProps

Theorem rest_word_typed_membership:
  well_typed_binop ann bop t1 t2 /\
  ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type t1) /\
  ~((bop = In \/ bop = NotIn) /\ ~is_word_type t1) /\
  ~(word_value_type t1 /\ word_value_type t2) /\
  ~((bop = Eq \/ bop = NotEq) /\
    (t1 = BaseT AddressT \/ ?m. t1 = BaseT (BytesT (Fixed m)))) ==>
  (bop = In \/ bop = NotIn) /\ is_word_type t1 /\
  (?bd. t2 = ArrayT t1 bd)
Proof
  Cases_on `bop` >>
  simp[well_typed_binop_def, word_value_type_def] >>
  rpt strip_tac >>
  gvs[is_numeric_type_def, is_int_type_def, is_bool_type_def,
      is_flag_type_def, is_word_type_def] >>~-
  ([`is_comparable_type t1`],
   Cases_on `t1` >>
   simp[is_comparable_type_def, is_bytestring_type_def,
        is_int_type_def, is_bool_type_def, is_flag_type_def] >>
   Cases_on `b` >>
   simp[is_bytestring_type_def, is_int_type_def, is_bool_type_def] >>
   rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  metis_tac[]
QED

Theorem rest_word_nonliteral_dispatch:
  (bop = In \/ bop = NotIn) /\
  expr_type e2 = ArrayT et bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
  compile_builtin_dispatch_body ce cenv ret_ty ty (Bop bop) [e1;e2] st =
    let (needle,st1) = lower_value ce cenv (expr_type e1) e1 st in
    let (arr_vv,st2) = ce cenv (expr_type e2) e2 st1 in
    as_stack_val ret_ty
      (compile_var_array_membership cenv needle arr_vv (expr_type e2)
         (bop = In) st2)
Proof
  strip_tac >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `e2` >> gvs[] >>
  rename1 `Builtin a bi elems` >> Cases_on `bi` >> gvs[]
QED

(* Source sequencing is already available in the ancestor exprBopSimProps:
   eval_expr_bop_bind rewrites bind(eval_expr Builtin)(read_result cx) to
   the two operand eval/read binds and bop_result, including BOTH failures.
   rest_word_mixed_marked_tail (ComposeTheory) uses exactly this equation.
   Do not duplicate it or make the successful second operand a premise here.
   To use rest_word_typed_membership with expr_body_pre, extract
   well_typed_binop using expr_body_pre_def, well_typed_expr_def and
   well_typed_builtin_app_def. Operand preconditions are already covered by
   expr_body_pre_builtin_arg; no duplicate of consumer expr_body_pre_bop.
*)
