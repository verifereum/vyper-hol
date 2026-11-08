# Slice source-frame checkpoint (C1.slice.frame)

SliceGuardFrame independently checks the exact E0255 Slice with literal start 0
and length 1. Its standalone source body_expr_ptr_ok is vacuous because standalone
Acc Code has no expr_body_pre. Its body_exprs_ptr_ok hypothesis holds for ANY tail,
because the six-witness source-success existential is false. Neither supplies a
judgment for the address or a compiler-first tail expression.

The complete enclosing expr_body_pre holds at order_ptr_env, order_ptr_cx,
order_ptr_tenv, order_ptr_source. Existing order_ptr_body_inv supplies the matching
source body frame. This includes the ABI/context clauses, not just typing and
allocation limits. slice_guard_frame_obligation specializes body_expr_ptr_ok to
both full pointer judgments for arbitrary d, PG, func, and ty. It assumes the
fixture body judgment, NOT the frozen target theorem (which remains admitted).

Remaining runtime boundary (bodyPtrDefs lines267-325):
- universally quantified sa,sb,op/vv,s0,G0,tn0 with exact lower_value/compile_expr
  equation; fn_has_code and fn_inst_ids_distinct;
- local_ptrs_reserved, no DALLOCA/constructor, old return-buffer/PC reservations;
- gas_admissible for eval_expr with expr_vv_res_ok, or eval/read bind with
  expr_res_ok; stmt_state_rel; ghost_inv for arbitrary G0,tn0; nonhalted PC at sa;
- a gas_outcome_ptr for that same computation/run, not an erased unrelated run.
  Normal posts include expr_post/vv_post, endpoint PC, ghost_inv, ptr_val_ok or
  ptr_vv_ok, memory buffer coverage and ghost_kept. Exceptional post is the
  original expr_exit res r, which must NOT be removed even for Div0 source.

No runtime premises above have been instantiated by this checkpoint. The
imported order-frame unit compiled another expression; it is not evidence that
this new fixture's code is installed. No unsafe tail or impossible exceptional
outcome is established. The literal-tail fixture might simply have a safe abort
path. Neither target falsehood nor the general Slice theorem follows.
