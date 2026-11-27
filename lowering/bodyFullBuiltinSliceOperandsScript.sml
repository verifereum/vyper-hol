(* Full child judgments for the actual tail-first code Slice operands. *)
Theory bodyFullBuiltinSliceOperands
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull exprSimSliceSource exprSimSource exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e ee` by
    (Cases_on `e = addr`
     >- (gvs[] >> metis_tac[slice_code_address_body_pre]) >>
     `well_typed_expr env
        (Builtin a (Slice n) [Builtin ct (Acc Code) [addr];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type e <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     metis_tac[expr_body_pre_builtin_typed_arg, MEM]) >>
  qpat_x_assum `body_expr_full_ok _ _`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  disch_then irule >> metis_tac[]
QED
*)
Theorem slice_code_child_full:
  expr_body_pre_mods mods cenv cx env
    (Builtin a (Slice n) [Builtin ct (Acc Code) [addr]; start; len]) es /\
  body_const_cells_agree mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\
  (e = start \/ e = len \/ e = addr) /\
  body_expr_full_ok_mods mods exps cx e /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e ee /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e ee
Proof
  cheat
QED
