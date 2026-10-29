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
 *   expr_sim_pre_struct_field, expr_sim_below_struct_fields,
 *   expr_sim_below_args — the children's preconditions and expr_ok
 *
 * Helpers: typed_value_wf, aggregate_named_child_syntax.
 *)
Theory exprSimAggregateSource
Ancestors
  exprSim exprSimAggregateChildren exprSimHyps
  vyperInterpreter vyperValueOperation vyperState vyperTyping
  valueEncoding valueEncodingProofs vyperStatePreservation
  vyperTypeSystem vyperTypeCallGraph list exprCallBounds
  vyperTypeEvalSoundness vyperTypeInvariants vyperExprNoControl
  vyperTypeExprSoundness vyperTypeExprResult

(* A captured storage place accepted by storage_holds reads to a value. *)
Theorem storage_holds_materialised:
  storage_holds cx trans t tv w es ==>
  ?v. read_result cx tv es = (INL v, es)
Proof
  simp[storage_holds_def] >> metis_tac[]
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
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (rr,es1)` >>
  Cases_on `rr` >> simp[] >> rename1 `read_result cx tv es1` >>
  Cases_on `read_result cx tv es1` >>
  rename1 `read_result cx tv es1 = (mr,es2)` >>
  `es2 = es1` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `mr` >> simp[] >>
  Cases_on `eval_exprs cx args es1` >>
  rename1 `eval_exprs cx args es1 = (rr,es3)` >>
  Cases_on `rr` >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem vv_post_materialises:
  vv_post func ce cx e es sa sb s0 es' tv vv r ==>
  ?v. read_result cx tv es' = (INL v,es')
Proof
  simp[vv_post_def] >> strip_tac >> Cases_on `vv` >>
  gvs[vv_holds_def] >>
  rename1 `LocatedValue ty p` >> Cases_on `p.ptr_location` >>
  gvs[vv_holds_def, immutable_holds_def, storage_holds_def] >>
  metis_tac[]
QED

Theorem aggregate_materialised_child_typed:
  expr_sim_pre ce cx env e es /\ eval_expr cx e es = (INL tv,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  read_result cx tv es' = (INL v,es') ==>
  value_has_type tyv v
Proof
  strip_tac >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,es')` by
    simp[bind_def] >>
  drule_all expr_sim_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def, value_runtime_typed_def]
QED

Theorem aggregate_child_res_ok:
  expr_sim_pre ce cx env e es /\ eval_expr cx e es = (res,es') ==>
  expr_vv_res_ok res
Proof
  metis_tac[expr_sim_pre_vv_res_ok]
QED

Theorem typed_value_wf:
  (!ty v. value_has_type ty v ==> val_wf ty v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv n kvs. sparse_has_type tv n kvs ==> kvs_val_wf kvs tv n) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!ftvs fields. struct_has_type ftvs fields ==> fields_val_wf fields ftvs)
Proof
  ho_match_mp_tac value_has_type_ind >>
  simp[value_has_type_def, val_wf_def, type_memory_size_def] >>
  rpt strip_tac >>
  qspec_then `max` assume_tac le_word_size_mul >> decide_tac
QED

Theorem aggregate_materialised_child_wf:
  expr_sim_pre ce cx env e es /\ eval_expr cx e es = (INL tv,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  read_result cx tv es' = (INL v,es') ==>
  val_wf tyv v
Proof
  strip_tac >> drule_all aggregate_materialised_child_typed >>
  metis_tac[cj 1 typed_value_wf]
QED

Theorem aggregate_eval_struct:
  eval_exprs cx (MAP SND fields) es = (res,es') ==>
  eval_expr cx (StructLit ann nsid fields) es =
    ((case res of
        INL vs => INL (Value (StructV (ZIP (MAP FST fields,vs))))
      | INR exc => INR exc),es')
Proof
  PairCases_on `nsid` >>
  simp[Once evaluate_def, bind_def, return_def] >>
  strip_tac >> simp[] >> Cases_on `res` >> simp[return_def]
QED

Theorem aggregate_named_child_syntax:
  !fields env ce e.
    well_typed_named_exprs env fields /\ byte_widths_named_exprs fields /\
    alloc_limits_named_exprs ce fields /\ int_calls_named_exprs fields = [] /\
    MEM e (MAP SND fields) ==>
    well_typed_expr env e /\ byte_widths_expr e /\
    alloc_limits_expr ce e /\ int_calls_expr e = []
Proof
  Induct_on `fields`
  >- simp[] >>
  Cases_on `h` >>
  simp[well_typed_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       int_calls_expr_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem expr_sim_pre_struct_field:
  !ce cx env ann nsid fields e es es'.
    expr_sim_pre ce cx env (StructLit ann nsid fields) es /\
    MEM e (MAP SND fields) /\ expr_sim_inv ce cx env es' /\
    source_supply es' ==>
    expr_sim_pre ce cx env e es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, byte_widths_expr_def,
     alloc_limits_expr_def, int_calls_expr_def] >>
  drule_all aggregate_named_child_syntax >> strip_tac >> gvs[]
QED

Theorem expr_sim_below_struct_fields:
  expr_sim_below ce (expr_size (StructLit ann nsid fields)) ==>
  EVERY (expr_ok ce) (MAP SND fields)
Proof
  rw[EVERY_MEM, MEM_MAP] >> Cases_on `y` >> gvs[] >>
  drule exprCallBoundsTheory.expr_struct_field_bound >>
  disch_then (qspecl_then [`nsid`,`ann`] mp_tac) >>
  gvs[expr_sim_below_def, vyperASTTheory.expr_size_def]
QED

Theorem expr_sim_below_args:
  expr_sim_below ce (list_size expr_size args) ==>
  EVERY (expr_ok ce) args
Proof
  simp[EVERY_MEM] >> metis_tac[expr_sim_below_mem]
QED

Theorem aggregate_eval_make_tuple:
  compatible_bound bnd (LENGTH args) /\
  eval_exprs cx args es = (rr,es') ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) args) es =
    ((case rr of INL vs => INL (Value (ArrayV (TupleV vs)))
      | INR exc => INR exc),es')
Proof
  strip_tac >>
  simp[Once evaluate_def, vyperContextTheory.builtin_args_length_ok_def, type_check_def,
    assert_def, ignore_bind_def, bind_def, return_def] >>
  Cases_on `rr` >>
  simp[get_accounts_def, lift_sum_def, vyperContextTheory.evaluate_builtin_def,
    return_def, raise_def, bind_def]
QED

Theorem aggregate_eval_make_array:
  compatible_bound bnd (LENGTH args) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  eval_exprs cx args es = (rr,es') ==>
  eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args) es =
    ((case rr of INL vs => INL (Value (ArrayV (make_array_value tv bnd vs)))
      | INR exc => INR exc),es')
Proof
  strip_tac >>
  simp[Once evaluate_def, vyperContextTheory.builtin_args_length_ok_def, type_check_def,
    assert_def, ignore_bind_def, bind_def, return_def] >>
  Cases_on `rr` >>
  simp[get_accounts_def, lift_sum_def, vyperContextTheory.evaluate_builtin_def,
    return_def, raise_def, bind_def]
QED
