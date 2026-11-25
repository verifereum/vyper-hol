(* Transport the body precondition to each actual operand of a code slice. *)
Theory s1PrefixBuiltinSliceChildPre
Ancestors
  exprSimSliceSource exprSimSource exprBodyPreProps

Theorem slice_code_child_body_pre:
  expr_body_pre cenv cx env
    (Builtin a (Slice n) [Builtin ct (Acc Code) [addr]; start; len]) es /\
  expr_sim_inv cenv cx env ee /\ (e = start \/ e = len \/ e = addr) ==>
  expr_body_pre cenv cx env e ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `e = addr`
  >- (gvs[] >> metis_tac[slice_code_address_body_pre]) >>
  drule expr_body_pre_static_facts >> strip_tac >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  `expr_type e <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
  metis_tac[expr_body_pre_builtin_typed_arg, listTheory.MEM]
QED
