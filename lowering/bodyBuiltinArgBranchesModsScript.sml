(* Operand callbacks justified by the evaluator's builtin arity check. *)
Theory bodyBuiltinArgBranchesMods
Ancestors
  bodyFullPredsMods vyperInterpreter vyperContext vyperState

Theorem len_operand_full_ok_mods:
  (!s'' x t.
     type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
     (INL x,t) /\ bt = Len ==>
     body_expr_full_ok_mods mods exps cx (HD es)) /\
  bt = Len /\ builtin_args_length_ok bt (LENGTH es) ==>
  body_expr_full_ok_mods mods exps cx (HD es)
Proof
  strip_tac >>
  qpat_x_assum `!s x t. _ ==> _`
    (qspecl_then [`ARB`, `()`, `ARB`] mp_tac) >>
  simp[type_check_def, assert_def]
QED

Theorem make_array_elements_full_ok_mods:
  (!s'' x t.
     type_check (builtin_args_length_ok (MakeArray ty n) (LENGTH es))
       "Builtin args" s'' = (INL x,t) /\
     MakeArray ty n <> Len /\ MakeArray ty n <> Env MsgGas /\
     code_slice_source (MakeArray ty n) es = NONE ==>
     body_exprs_full_ok_mods mods exps cx es) /\
  builtin_args_length_ok (MakeArray ty n) (LENGTH es) ==>
  body_exprs_full_ok_mods mods exps cx es
Proof
  strip_tac >>
  `code_slice_source (MakeArray ty n) es = NONE` by
    (Cases_on `code_slice_source (MakeArray ty n) es` >> simp[] >>
     PairCases_on `x` >> gvs[code_slice_source_SOME]) >>
  qpat_x_assum `!s x t. _ ==> _`
    (qspecl_then [`ARB`, `()`, `ARB`] mp_tac) >>
  simp[type_check_def, assert_def]
QED
