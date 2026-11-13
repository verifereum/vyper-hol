(*
 * The pointer twin of S1's bodySimStructLitWidened: a struct literal with
 * an element whose post describes its value at a type other than its
 * annotated one (post_value_type: an internal call whose type widens its
 * callee's return type), for bodyPtrStructLit's structlit_expr_ptr_ok.
 *
 * RESIDUAL, HELD with S1's body_struct_lit_widened_call_elem: describing
 * such an element's value at its annotated type is the internal-call
 * simulation's work.  Not open work here.
 *
 * TOP-LEVEL:
 *   body_struct_lit_widened_call_elem_ptr - that case
 *)
Theory bodyPtrStructLitWidened
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* RESIDUAL: widened internal-call struct element, held with S1's
   body_struct_lit_widened_call_elem *)
Theorem body_struct_lit_widened_call_elem_ptr:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ptr_ok cx (MAP SND kes)) ==>
    !d PG tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      EXISTS (\e. post_value_type cenv e <> expr_type e) (MAP SND kes) ==>
      expr_sim_ptr d ctx PG func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  cheat
QED
