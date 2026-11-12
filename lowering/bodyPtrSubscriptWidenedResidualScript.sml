(*
 * RESIDUAL of bodyPtrSubscript's subscript_expr_ptr_ok: a subscript whose
 * base value the lowering lays out at another type than the base's.  The
 * pointer twin of S1's body_subscript_widened_call_base
 * (bodySimSubscriptWidened), which S1 admits too: an internal call whose
 * callee's return type the call site widens (f() -> (Bytes[1], uint256)
 * used as (Bytes[128], uint256)) hands back the callee's return buffer,
 * laid out at the declared type, while compile_subscript reads the base at
 * offsets and sizes taken from the base's annotated type, so the element
 * pointer and its buffer coverage are those of the wider layout.  It
 * belongs to the widened-call wave, with its S1 twin.
 *
 * TOP-LEVEL:
 *   body_subscript_widened_call_base_ptr
 *)
Theory bodyPtrSubscriptWidenedResidual
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts
  vyperInterpreter vyperState vyperContext vyperAST

Theorem body_subscript_widened_call_base_ptr:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 ==>
    !d PG tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Subscript v8 e1 e2) es /\
      post_value_type cenv e1 <> expr_type e1 ==>
      expr_sim_ptr d ctx PG func cenv cx ty (Subscript v8 e1 e2) es /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript v8 e1 e2) es
Proof
  (* RESIDUAL: held per argon ruling 2026-11-08 for the widened-call wave,
     as S1 holds its twin *)
  cheat
QED
