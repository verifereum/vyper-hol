(* Complete identity unwrap continuations at the post-ADD cursor. *)
Theory bodyPtrStructLitIdentityRead
Ancestors
  bodyPtrStructLitUnwrap exprSimUnwrap exprSimUnwrapProps
  bodyPtrDefs gasSummaryComposePtr gasSummary loweringPosts

Theorem marked_identity_source:
  gas_marked_exec_ptr D (ctx,fn) PG source (ee,s,G,tn) []
    res ee G tn (OK s) ==>
  source ee = (res,ee)
Proof
  simp[gas_marked_exec_ptr_def, gas_explicit_def] >> strip_tac >>
  first_x_assum (qspec_then `ee.gas_obs` mp_tac) >> simp[]
QED

Theorem stack_unwrap_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (StackValue ty op) s /\
  ptr_vv_ok cx (expr_type e) tv (StackValue ty op) ee G tn s /\
  unwrap_value cenv (StackValue ty op) sm = (out,sb) /\ ~s.vs_halted ==>
  sb = sm /\ out = op /\
  ?v. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G tn (OK s) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v out s /\
    ptr_val_ok cx (expr_type e) v out G tn s
Proof
  strip_tac >> drule_all stack_unwrap_counted >>
  disch_then (qspecl_then [`D`, `ctx`, `fn`, `PG`] strip_assume_tac) >> gvs[] >>
  drule marked_identity_source >> strip_tac >>
  `vv_post ctx fn cenv cx e es sa sb s0 ee (Value v) (StackValue ty op) s`
    by metis_tac[vv_post_read_result] >>
  simp[] >> metis_tac[expr_post_of_vv_post_stack]
QED

Theorem memory_nonword_unwrap_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) ee G tn s /\
  unwrap_value cenv (LocatedValue ty p) sm = (out,sb) /\ ~s.vs_halted /\
  ~is_word_type ty /\ p.ptr_location = LocMemory /\
  (is_word_type (expr_type e) ==> op_prov G p.ptr_operand = NONE) ==>
  sb = sm /\ out = p.ptr_operand /\
  ?v. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G tn (OK s) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v out s /\
    ptr_val_ok cx (expr_type e) v out G tn s
Proof
  strip_tac >> drule_all memory_nonword_unwrap_counted >>
  disch_then (qspecl_then [`D`, `ctx`, `fn`, `PG`] strip_assume_tac) >> gvs[] >>
  drule marked_identity_source >> strip_tac >>
  `vv_post ctx fn cenv cx e es sa sb s0 ee (Value v) (LocatedValue ty p) s`
    by metis_tac[vv_post_read_result] >>
  simp[] >> metis_tac[expr_post_of_vv_post_memory]
QED
