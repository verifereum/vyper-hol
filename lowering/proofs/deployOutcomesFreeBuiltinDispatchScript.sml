Theory deployOutcomesFreeBuiltinDispatch
Ancestors exprLowering

(* Expose the shallow Name/list frontier before unfolding the compiled match. *)
Theorem outcomes_free_builtin_dispatch:
  Q (SND (bc ce t ty bi args s)) /\ Q s /\
  (!ce rt at a bt b mt m s. Q s ==>
    Q (SND (compile_addmod_names ce rt at a bt b mt m s))) /\
  (!ce rt at a bt b mt m s. Q s ==>
    Q (SND (compile_mulmod_names ce rt at a bt b mt m s))) /\
  (!ce rt at a bt b s. Q s ==>
    Q (SND (compile_powmod256_names ce rt at a bt b s))) ==>
  Q (SND (compile_expr_body f bc tc ce ty (Builtin t bi args) s))
Proof
  strip_tac >> namedCases_on `args` ["", "a rest"]
  >- simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `a` >>
  fs[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  namedCases_on `rest` ["", "b rest2"] >>
  fs[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `b` >>
  fs[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  namedCases_on `rest2` ["", "c rest3"]
  >- (Cases_on `bi` >>
      fs[compile_expr_body_def, vyperASTTheory.expr_type_def]) >>
  Cases_on `c` >>
  fs[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `rest3` >>
  fs[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  Cases_on `bi` >>
  fs[compile_expr_body_def, vyperASTTheory.expr_type_def]
QED
