Theory exprLoweringEquations
Ancestors exprLowering

Theorem compile_expr_body_builtin_default:
  ~(?at a bt b mt m. bi = AddMod /\ es = [Name at a; Name bt b; Name mt m]) /\
  ~(?at a bt b mt m. bi = MulMod /\ es = [Name at a; Name bt b; Name mt m]) /\
  ~(?at a bt b. bi = PowMod256 /\ es = [Name at a; Name bt b]) ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi es) = bfn ce ann ty bi es
Proof
  strip_tac >> Cases_on `es`
  >- simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >>
  rename1 `h::rest` >> Cases_on `h`
  >> TRY (simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >> NO_TAC) >>
  Cases_on `rest`
  >- simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >>
  rename1 `Name at a :: h :: rest` >> Cases_on `h`
  >> TRY (simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >> NO_TAC) >>
  Cases_on `rest`
  >- (Cases_on `bi` >> gvs[FUN_EQ_THM, compile_expr_body_def, expr_type_def]) >>
  rename1 `Name at a :: Name bt b :: h :: rest` >> Cases_on `h`
  >> TRY (simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >> NO_TAC) >>
  Cases_on `rest` >> Cases_on `bi` >> gvs[FUN_EQ_THM, compile_expr_body_def, expr_type_def]
QED
