Theory exprLoweringEquations
Ancestors exprLowering compileEnv vyperAST

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

Theorem compile_multi_vvs_length:
  !args cfn cenv st vs st'.
    compile_multi_vvs cfn cenv args st = (vs, st') ==>
    LENGTH vs = LENGTH args
Proof
  Induct >> simp[compile_multi_vvs_def, comp_return_def] >>
  rpt gen_tac >>
  simp[comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> simp[comp_return_def] >>
  Cases_on `compile_multi_vvs cfn cenv args cs'` >>
  simp[] >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED
