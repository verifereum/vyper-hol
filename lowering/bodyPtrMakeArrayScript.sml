(*
 * Array and tuple literals.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   make_array_expr_ptr_ok
 *)
Theory bodyPtrMakeArray
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  bodyPtrMakeArrayWidened bodyPtrMakeArrayPackage exprSimSource
  vyperTypeSystem vyperTypeBuiltins exprSimHypsDefs
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem make_array_expr_ptr_ok:
  !cx ty bt es.
    (?t n. bt = MakeArray t n) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  once_rewrite_tac[body_expr_ptr_ok_def] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `!e. MEM e es ==> int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`
  >- (`builtin_args_length_ok (MakeArray t n) (LENGTH es)` by
        (fs[expr_body_pre_def, well_typed_expr_def] >>
         drule well_typed_builtin_app_length >> simp[]) >>
      `body_exprs_ptr_ok cx es` by metis_tac[] >>
      `!e st. MEM e es /\ expr_sim_inv cenv cx env st ==>
         expr_body_pre cenv cx env e st` by
        (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
         goal_assum (drule_at Any) >> simp[] >>
         qexistsl [`ty`, `es`, `MakeArray t n`, `es'`] >> simp[]) >>
      `expr_vv_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (MakeArray t n) es) es'` by
        (Cases_on `t` >>
         metis_tac[literal_tuple_vv_sim_ptr, literal_array_vv_sim_ptr]) >>
      metis_tac[expr_sim_ptr_of_vv]) >>
  metis_tac[body_make_array_widened_call_elem_ptr]
QED
