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
  cheat
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
  cheat
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
  cheat
QED

Theorem well_typed_binop_word_result:
  !ann bop t1 t2.
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 ==>
    is_word_type ann
Proof
  cheat
QED

(* A well-typed binary operator has two operands. *)
Theorem expr_body_pre_bop_args:
  !cenv cx env ann bop args es.
    expr_body_pre cenv cx env (Builtin ann (Bop bop) args) es ==>
    ?e1 e2. args = [e1; e2]
Proof
  cheat
QED

Theorem expr_body_pre_bop:
  !cenv cx env ann bop e1 e2 es.
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    expr_body_pre cenv cx env e1 es /\
    !es'. expr_sim_inv cenv cx env es' ==> expr_body_pre cenv cx env e2 es'
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
  cheat
QED

Theorem expr_sim_ok_apply:
  !ctx func cenv cx env ty e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    expr_sim ctx func cenv cx ty e es
Proof
  cheat
QED

(* The operands' internal calls: none if the operator has none. *)
Theorem int_calls_bop_operands[local]:
  !nocalls ann bop e1 e2.
    (nocalls ==> int_calls_expr (Builtin ann (Bop bop) [e1; e2]) = []) ==>
    (nocalls ==> int_calls_expr e1 = []) /\
    (nocalls ==> int_calls_expr e2 = [])
Proof
  cheat
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
  cheat
QED

Theorem compile_bop_word_sim:
  !cenv ann bop e1 e2.
    expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) [e1; e2])
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem compile_bop_bytes_eq_sim:
  !cenv ann bop e1 e2.
    expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2 /\ (bop = Eq \/ bop = NotEq) /\
    (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m))) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) [e1; e2])
Proof
  cheat
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
  cheat
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
  cheat
QED

(* ===== All binary operators ===== *)

Theorem stack_value_pair_exists[local]:
  ?t op sb. (StackValue a x, y) = (StackValue t op, sb)
Proof
  cheat
QED

(* A binary operator is lowered to a StackValue. *)
Theorem compile_bop_stack:
  !cenv ty ann bop args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann (Bop bop) args) sa =
              (StackValue t op, sb)
Proof
  cheat
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
  cheat
QED

(* An ill-typed binary operator, without two operands, meets no
   expr_body_pre. *)
Theorem compile_bop_args_case:
  !nocalls ctx func cenv cx ann bop args.
    (!e1 e2. args <> [e1; e2]) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) args) /\
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Bop bop) args)
Proof
  cheat
QED

Theorem compile_bop_ok:
  !cenv ann bop args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_ok cenv (Builtin ann (Bop bop) args)
Proof
  cheat
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
  cheat
QED

(* not: ISZERO, NOT or the flag mask's XOR on the operand
   (exprSimUnop's compile_not_frag); the operand's compile-state shape is
   lower_value_word_shape's. *)
Theorem compile_not_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Not args)
Proof
  cheat
QED

Theorem expr_body_pre_neg:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann Neg args) es ==>
    ?e1. args = [e1] /\ ann = expr_type e1 /\
      is_numeric_type (expr_type e1) /\ ~is_uint_type (expr_type e1) /\
      expr_body_pre cenv cx env e1 es
Proof
  cheat
QED

Theorem compile_neg_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Neg args)
Proof
  cheat
QED

(* abs: compile_builtin_abs on the operand (exprSimUnop's
   compile_abs_frag); the operand's compile-state shape is
   lower_value_word_shape's. *)
Theorem compile_abs_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Abs args)
Proof
  cheat
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
  cheat
QED

Theorem expr_sim_pre_ifexp:
  !cenv cx env t c a b es.
    expr_sim_pre cenv cx env (IfExp t c a b) es ==>
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    expr_sim_pre cenv cx env c es /\
    !es'. expr_sim_inv cenv cx env es' ==>
          expr_sim_pre cenv cx env a es' /\ expr_sim_pre cenv cx env b es'
Proof
  cheat
QED

(* A conditional retains a place only for a memory aggregate. *)
Theorem word_type_conditional_result_value:
  !t env cx st source x.
    is_word_type t /\ eval_result_typed (env,cx,st) x (Type t) /\
    conditional_result cx source st = (INL x,st) ==>
    is_Value x
Proof
  cheat
QED

Theorem expr_body_pre_ifexp_word_readable:
  !cenv cx env t c a b es res es'.
    expr_body_pre cenv cx env (IfExp t c a b) es /\ is_word_type t /\
    eval_expr cx (IfExp t c a b) es = (res,es') ==>
    expr_read_res_ok cx es' res
Proof
  cheat
QED

(* The operands' internal calls: none if the conditional has none. *)
Theorem int_calls_ifexp_operands[local]:
  !nocalls t c a b.
    (nocalls ==> int_calls_expr (IfExp t c a b) = []) ==>
    (nocalls ==> int_calls_expr c = []) /\
    (nocalls ==> int_calls_expr a = []) /\
    (nocalls ==> int_calls_expr b = [])
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem compile_ifexp_sim:
  !cenv ann c e1 e2.
    expr_sim_below cenv (expr_size (IfExp ann c e1 e2)) ==>
    expr_vv_ok cenv (IfExp ann c e1 e2)
Proof
  cheat
QED
