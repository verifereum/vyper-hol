(* Arity checks select reached operands, without making the address of a
   code slice available before the tail has succeeded. *)
Theory bodyAggregateArityMods
Ancestors
  bodyFullPredsMods vyperInterpreter vyperContext vyperState

Theorem type_builtin_args_at_arity_mods:
  (!s x t.
    type_check (type_builtin_args_length_ok tb (LENGTH es))
      "TypeBuiltin args" s = (INL x,t) ==>
    body_exprs_full_ok_mods mods exps cx es) ==>
  type_builtin_args_length_ok tb (LENGTH es) ==>
  body_exprs_full_ok_mods mods exps cx es
Proof
  rpt disch_tac >>
  first_x_assum (qspecl_then [`ARB`, `()`, `ARB`] mp_tac) >>
  simp[type_check_def, assert_def]
QED

Theorem code_slice_args_at_arity_mods:
  (!s x t v code_ty addr tail_s tail_vs t'.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s =
      (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
    code_slice_source bt es = SOME v /\ v = (code_ty,addr) /\
    eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
    body_exprs_full_ok_mods mods exps cx [addr]) /\
  (!s x t v code_ty addr.
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s =
      (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
    code_slice_source bt es = SOME v /\ v = (code_ty,addr) ==>
    body_exprs_full_ok_mods mods exps cx (TL es)) /\
  code_slice_source bt es = SOME (ct,a) ==>
  builtin_args_length_ok bt (LENGTH es) ==>
  body_exprs_full_ok_mods mods exps cx (TL es) /\
  (!tail_s tail_vs t'. eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
    body_exprs_full_ok_mods mods exps cx [a])
Proof
  strip_tac >> disch_tac >>
  `bt <> Len /\ bt <> Env MsgGas` by
    (qpat_assum `code_slice_source _ _ = SOME _` mp_tac >>
     simp[code_slice_source_SOME] >> strip_tac >> simp[]) >>
  `type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" ARB =
     (INL (), ARB)` by simp[type_check_def, assert_def] >>
  conj_tac
  >- (qpat_assum `!s x t v ct a. _ ==> body_exprs_full_ok_mods _ _ _ (TL _)`
        (fn th => drule th) >>
      disch_then (qspecl_then [`(ct,a)`, `ct`, `a`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!s x t v ct a ts vs t'. _ ==> body_exprs_full_ok_mods _ _ _ [_]`
    (fn th => drule th) >>
  disch_then (qspecl_then [`(ct,a)`, `ct`, `a`] mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED
