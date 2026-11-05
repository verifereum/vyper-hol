(* Admissibility boundary for account-member memory simulation. *)
Theory bodyMemBiAccCompose
Ancestors
  bodyMemoryPreds exprSimSource exprSimAccounts exprSimHypsDefs allocLimits
  vyperTyping vyperTypeSystem vyperAST

Theorem body_acc_mem_admissible:
  expr_body_pre cenv cx env (Builtin ty (Acc item) es) s ==>
  item <> Code /\
  ?e. es = [e] /\ ty = account_item_type item /\
      expr_type e = BaseT AddressT
Proof
  strip_tac >>
  `item <> Code` by
    (strip_tac >>
     gvs[expr_body_pre_def, alloc_limits_expr_def]) >>
  simp[] >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `es` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]
QED
