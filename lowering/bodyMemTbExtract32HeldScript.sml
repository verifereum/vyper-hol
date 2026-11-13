(* Memory case of the body induction for extract32 outside a dynamic Bytes
   source with an unsigned start.  Vacuous: extract32's typing
   (well_typed_type_builtin_args_def) requires exactly that shape. *)
Theory bodyMemTbExtract32Held
Ancestors
  bodyMemoryPreds

Theorem body_type_builtin_extract32_other_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) /\
    ~(?src off m k. es = [src; off] /\
        expr_type src = BaseT (BytesT (Dynamic m)) /\
        expr_type off = BaseT (UintT k)) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ es)
Proof
  rw[body_expr_mem_ok_def, exprSimHypsDefsTheory.expr_body_pre_def] >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_type_builtin_args_def] >>
  Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  metis_tac[]
QED
