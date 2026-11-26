(* Request-prefix companion to bodyFullBuiltinSliceOperands. *)
Theory s1PrefixBuiltinSliceOperands
Ancestors
  s1PrefixPreds bodyFullBuiltinSliceOperands s1PrefixDefs

Theorem slice_code_child_prefix:
  expr_body_pre cenv cx env
    (Builtin a (Slice n) [Builtin ct (Acc Code) [addr]; start; len]) es /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_sim_inv cenv cx env ee /\
  (e = start \/ e = len \/ e = addr) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e ee /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e ee` by
    (Cases_on `e = addr`
     >- (gvs[] >> metis_tac[exprSimSliceSourceTheory.slice_code_address_body_pre]) >>
     `well_typed_expr env
        (Builtin a (Slice n) [Builtin ct (Acc Code) [addr];start;len])` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule exprSimSliceSourceTheory.slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type e <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_builtin_typed_arg, listTheory.MEM]) >>
  qpat_x_assum `body_expr_prefix_ok _ _`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  disch_then irule >> metis_tac[]
QED
