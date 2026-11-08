(* Conditional consumer bridge: actual-unit header exclusion remains explicit. *)
Theory bodyPtrBytestringBuiltinsConcatConditional
Ancestors
  bodyPtrBytestringBuiltinsConcatCompatibility
  bodyPtrBytestringBuiltinsConcatProgramProbe bodyPtrDefs bodyPtrPreds
  exprPtrUnwrap

Theorem concat_vv_ptr_of_context_header_free:
  (!f. lookup_function f.fn_name ctx.ctx_functions = SOME f ==>
       concat_header_free f) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx out_ty (Builtin ann (Concat n) args) es
Proof
  rw[expr_vv_sim_ptr_def] >>
  drule stmt_state_rel_function_lookup >> strip_tac >>
  drule_all compile_concat_mandatory_header >>
  metis_tac[]
QED

Theorem concat_body_ptr_of_context_header_free:
  (!tops ctx cenv env es.
     body_inv tops ctx cenv cx /\
     expr_body_pre cenv cx env (Builtin ann (Concat n) args) es ==>
     !f. lookup_function f.fn_name ctx.ctx_functions = SOME f ==>
         concat_header_free f) ==>
  body_expr_ptr_ok cx (Builtin ann (Concat n) args)
Proof
  rw[body_expr_ptr_ok_def] >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin ann (Concat n) args) es` by
    (irule concat_vv_ptr_of_context_header_free >> metis_tac[]) >>
  metis_tac[expr_sim_ptr_of_vv]
QED
