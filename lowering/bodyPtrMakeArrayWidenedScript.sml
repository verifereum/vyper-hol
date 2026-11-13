(*
 * The pointer twin of S1's bodySimMakeArrayWidened: an array literal with
 * an element that is an internal call whose lowered value type differs
 * from its annotated type, for bodyPtrMakeArray's make_array_expr_ptr_ok.
 *
 * Child pointer facts describe the physical post type.  Each literal slot
 * receives a typed store into the container's declared member layout.
 *
 * TOP-LEVEL:
 *   body_make_array_widened_call_elem_ptr - that case
 *)
Theory bodyPtrMakeArrayWidened
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  bodyPtrPhysicalLiteralPackage exprSimSource vyperTypeSystem vyperTypeBuiltins
  exprSimHypsDefs
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem body_make_array_widened_call_elem_ptr:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    !d PG tops ctx func cenv env ty' st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
      (?e. MEM e es /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok (MakeArray t n) (LENGTH es)` by
    (fs[expr_body_pre_def, well_typed_expr_def] >>
     drule well_typed_builtin_app_length >> simp[]) >>
  `body_exprs_ptr_ok cx es` by metis_tac[] >>
  `!e st'. MEM e es /\ expr_sim_inv cenv cx env st' ==>
     expr_body_pre cenv cx env e st'` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`ty`, `es`, `MakeArray t n`, `st`] >> simp[]) >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (MakeArray t n) es) st` by
    (Cases_on `t` >>
     metis_tac[literal_tuple_vv_sim_ptr_physical, literal_array_vv_sim_ptr_physical]) >>
  metis_tac[expr_sim_ptr_of_vv]
QED
