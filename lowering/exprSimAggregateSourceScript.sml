(*
 * Source evaluation of aggregate literals (#636)
 *
 * eval_exprs evaluates and materialises each child before the next, the
 * order the lowering stores them in, so a literal's value is the list of
 * its children's.  Also the typing of a materialised child, and the
 * induction hypothesis restricted to the children.
 *
 * TOP-LEVEL:
 *   aggregate_eval_exprs_cons — eval_exprs on e::args
 *   aggregate_eval_struct, aggregate_eval_make_tuple,
 *   aggregate_eval_make_array — a literal's value from its children's
 *   storage_holds_materialised, vv_post_materialises — a child's result
 *     materialises
 *   aggregate_materialised_child_typed, aggregate_materialised_child_wf,
 *   aggregate_child_res_ok — the materialised value is typed and val_wf
 *   expr_sim_pre_struct_field, expr_body_pre_struct_field,
 *   expr_sim_below_struct_fields, expr_sim_below_args — the children's
 *   preconditions and expr_ok
 *
 * Helpers: typed_value_wf, aggregate_named_child_body_syntax.
 *)
Theory exprSimAggregateSource
Ancestors
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  loweringPosts
  allocLimits
   exprSimAggregateChildren exprSimHyps
  vyperInterpreter vyperValueOperation vyperState vyperTyping
  valueEncoding valueEncodingProofs vyperStatePreservation
  vyperTypeSystem vyperTypeCallGraph list exprCallBounds
  vyperTypeEvalSoundness vyperTypeInvariants vyperExprNoControl
  vyperTypeExprSoundness vyperTypeExprResult

(* A captured storage place accepted by storage_holds reads to a value. *)
Theorem storage_holds_materialised:
  storage_holds cx trans t tv w es s ==>
  ?v. read_result cx tv es = (INL v, es)
Proof
  cheat
QED

Theorem aggregate_eval_exprs_cons:
  eval_exprs cx (e::args) es = (res,es') ==>
  (?exc. eval_expr cx e es = (INR exc,es') /\ res = INR exc) \/
  (?tv es1 exc. eval_expr cx e es = (INL tv,es1) /\
    read_result cx tv es1 = (INR exc,es') /\ res = INR exc) \/
  (?tv es1 v rr. eval_expr cx e es = (INL tv,es1) /\
    read_result cx tv es1 = (INL v,es1) /\
    eval_exprs cx args es1 = (rr,es') /\
    res = (case rr of INL vs => INL (v::vs) | INR exc => INR exc))
Proof
  cheat
QED

Theorem vv_post_materialises:
  vv_post ctx func ce cx e es sa sb s0 es' tv vv r ==>
  ?v. read_result cx tv es' = (INL v,es')
Proof
  cheat
QED

Theorem aggregate_materialised_child_typed:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL tv,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  read_result cx tv es' = (INL v,es') ==>
  value_has_type tyv v
Proof
  cheat
QED

Theorem aggregate_child_res_ok:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (res,es') ==>
  expr_vv_res_ok res
Proof
  cheat
QED


Theorem aggregate_materialised_child_wf:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL tv,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  read_result cx tv es' = (INL v,es') ==>
  val_wf tyv v
Proof
  cheat
QED

Theorem aggregate_eval_struct:
  eval_exprs cx (MAP SND fields) es = (res,es') ==>
  eval_expr cx (StructLit ann nsid fields) es =
    ((case res of
        INL vs => INL (Value (StructV (ZIP (MAP FST fields,vs))))
      | INR exc => INR exc),es')
Proof
  cheat
QED

Theorem aggregate_named_child_body_syntax:
  !fields env ce e.
    well_typed_named_exprs env fields /\ byte_widths_named_exprs fields /\
    alloc_limits_named_exprs ce fields /\ MEM e (MAP SND fields) ==>
    well_typed_expr env e /\ byte_widths_expr e /\ alloc_limits_expr ce e /\
    !c. MEM c (int_calls_expr e) ==> MEM c (int_calls_named_exprs fields)
Proof
  cheat
QED

(* A field meets expr_body_pre wherever expr_sim_inv holds, and has no
   internal call where the literal has none. *)
Theorem expr_body_pre_struct_field:
  !ce cx env ann nsid fields e es es'.
    expr_body_pre ce cx env (StructLit ann nsid fields) es /\
    MEM e (MAP SND fields) /\ expr_sim_inv ce cx env es' ==>
    expr_body_pre ce cx env e es' /\
    (int_calls_expr (StructLit ann nsid fields) = [] ==>
     int_calls_expr e = [])
Proof
  cheat
QED

Theorem expr_sim_pre_struct_field:
  !ce cx env ann nsid fields e es es'.
    expr_sim_pre ce cx env (StructLit ann nsid fields) es /\
    MEM e (MAP SND fields) /\ expr_sim_inv ce cx env es' ==>
    expr_sim_pre ce cx env e es'
Proof
  cheat
QED

Theorem expr_sim_below_struct_fields:
  expr_sim_below ce (expr_size (StructLit ann nsid fields)) ==>
  EVERY (expr_ok ce) (MAP SND fields)
Proof
  cheat
QED

Theorem expr_sim_below_args:
  expr_sim_below ce (list_size expr_size args) ==>
  EVERY (expr_ok ce) args
Proof
  cheat
QED

Theorem aggregate_eval_make_tuple:
  compatible_bound bnd (LENGTH args) /\
  eval_exprs cx args es = (rr,es') ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) args) es =
    ((case rr of INL vs => INL (Value (ArrayV (TupleV vs)))
      | INR exc => INR exc),es')
Proof
  cheat
QED

Theorem aggregate_eval_make_array:
  compatible_bound bnd (LENGTH args) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  eval_exprs cx args es = (rr,es') ==>
  eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args) es =
    ((case rr of INL vs => INL (Value (ArrayV (make_array_value tv bnd vs)))
      | INR exc => INR exc),es')
Proof
  cheat
QED
