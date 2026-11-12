(* An effect-free expression's ordinary value post already gives its
   internal-call argument provenance, unless its value is in code or its
   type contains a dynamic array. *)
Theory bodyIntCallPostProvenance
Ancestors
  bodyIntCallProducerInterface bodyIntCallArgType bodyIntCallArgEligibility loweringPosts

Theorem vv_post_intcall_provenance:
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
  ~expr_has_effect e /\
  (!t' p. vv = LocatedValue t' p ==> p.ptr_location <> LocCode) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
         dynarray_free tvt) ==>
  intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv vv t
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[effect_free_post_value_type] >>
  gvs[vv_post_def, intcall_vv_provenance_def] >>
  Cases_on `vv` >> gvs[vv_at_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED

(* Held (argon, s1-calls branch): the cases vv_post_intcall_provenance
   leaves out, an effect-free argument whose value is a code pointer
   (an immutable or a selection from one) or whose type contains a
   dynamic array.  Its run's success post also gives the argument's
   provenance: a borrowed local or immutable selection is a sub_layout of
   that variable's value, and anything else lies in its own ALLOCAs.  Only
   the frozen lowering's evaluate-all-then-stage order needs this; on
   trunk, eager staging of each memory argument (vyper-hol#1217) retires
   it. *)
Theorem intcall_arg_provenance_held:
  body_inv tops ctx cenv cx /\ body_expr_ok cx e /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ((?t' p. vv = LocatedValue t' p /\ p.ptr_location = LocCode) \/
   (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          ~dynarray_free tvt)) /\
  compile_expr cenv (expr_type e) e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  cheat
QED
