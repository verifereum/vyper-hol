(*
 * in and not in, on array literals and on arrays.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   bop_in_expr_ptr_ok
 *)
Theory bodyPtrBopIn
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list
  bodyPtrBopInHeld bodyPtrBopInFlagBody bodyPtrBopInLiteralBody
  bodyPtrBopInNonliteralBody exprSimOperators exprSimSource vyperTypeSystem
  exprSimHypsDefs

val _ = Parse.hide "body";

Theorem bop_in_expr_ptr_ok:
  !cx ty bop es.
    (bop = In \/ bop = NotIn) /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_args >> strip_tac >> gnvs[] >>
  `body_exprs_ptr_ok cx [e1;e2]` by fs[builtin_args_length_ok_def] >>
  Cases_on `is_word_type (expr_type e1)`
  >- (drule expr_body_pre_bop >> strip_tac >>
      `(?fid. expr_type e2 = FlagT fid) \/
       (?bd. expr_type e2 = ArrayT (expr_type e1) bd)` by
        (Cases_on `bop` >> gvs[well_typed_binop_def] >> metis_tac[]) >>
      pop_assum strip_assume_tac
      >- (`body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])` by
            (irule membership_flag_ptr_ok >> simp[] >> metis_tac[]) >>
          fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
      Cases_on `?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- (pop_assum strip_assume_tac >> gnvs[] >>
          `expr_body_pre cenv cx env (Builtin a (MakeArray t n) elems) es'` by
            metis_tac[expr_body_pre_def] >>
          `builtin_args_length_ok (MakeArray t n) (LENGTH elems)` by
            (Cases_on `t` >>
             gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
                 builtin_args_length_ok_def]) >>
          `body_exprs_ptr_ok cx (e1::elems)` by
            (fs[body_exprs_ptr_ok_def] >> rpt strip_tac >>
             irule body_make_array_children_ptr_ok >> simp[] >> metis_tac[]) >>
          `body_expr_ptr_ok cx
            (Builtin ty (Bop bop) [e1;Builtin a (MakeArray t n) elems])` by
            (irule body_bop_in_literal_ptr_ok >> simp[]) >>
          fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
      `body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])` by
        (irule body_bop_in_nonliteral_word_ptr_ok >> simp[] >> metis_tac[]) >>
      fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
  `body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])` by
    (irule bop_in_nonword_ptr_ok >> simp[]) >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED
