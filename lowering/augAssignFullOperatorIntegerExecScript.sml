Theory augAssignFullOperatorIntegerExec
Ancestors bodyPtrBopScalarRun exprSimBinopFrag valueEncoding

Theorem augassign_integer_execution:
  !cx bop ty bl el tys v1 v2 es tenv tv x y sa op sb s.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ is_int_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 /\
    expr_res_ok (bop_result cx ty bop tys v1 v2 es) /\
    compile_binop bop x y ty bl el sa = (op,sb) /\
    fresh_vars_wrt sa s /\
    eval_operand x s = SOME (val_to_w256 v1) /\
    eval_operand y s = SOME (val_to_w256 v2) ==>
    (?v t. bop_result cx ty bop tys v1 v2 es = INL v /\
      word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
    (?m t. bop_result cx ty bop tys v1 v2 es =
        INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> gvs[val_to_w256_def]
  >~ [`bop_result _ _ Div`] >-
    (irule bop_divmod_fresh_run >> simp[] >> goal_assum (drule_at Any) >> metis_tac[])
  >~ [`bop_result _ _ Mod`] >-
    (irule bop_divmod_fresh_run >> simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule bop_checked_fresh_run >> simp[] >> goal_assum (drule_at Any) >> metis_tac[]
QED
