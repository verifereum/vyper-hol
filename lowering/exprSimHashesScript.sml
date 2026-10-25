Theory exprSimHashes
Ancestors
  arithmetic list words exprSimHyps exprLowering exprLoweringProps
  compileEnv vyperAST vyperInterpreter vyperContext vyperTypeSystem
  vyperState vyperValue exprBopLowering
Libs
  pairLib

Theorem well_typed_keccak256_args:
  !ann args.
    well_typed_builtin_app ann Keccak256 (MAP expr_type args) ==>
    ?e. args = [e] /\ ann = BaseT (BytesT (Fixed 32)) /\
        ((?m. expr_type e = BaseT (BytesT (Fixed m))) \/
         (?n. expr_type e = BaseT (BytesT (Dynamic n))) \/
         (?n. expr_type e = BaseT (StringT n)))
Proof
  rpt gen_tac >> simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  rename1 `is_bytes_or_string_type (expr_type e)` >>
  Cases_on `expr_type e` >> gvs[] >>
  rename1 `is_bytes_or_string_type (BaseT bt)` >>
  Cases_on `bt` >> gvs[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[]
QED

Theorem eval_expr_keccak256_cases:
  !cx ann e es res es'.
    eval_expr cx (Builtin ann Keccak256 [e]) es = (res, es') ==>
    (?exc. eval_expr cx e es = (INR exc, es') /\ res = INR exc) \/
    (?tv es1. eval_expr cx e es = (INL tv, es1) /\ !v. tv <> Value v) \/
    ?v. eval_expr cx e es = (INL (Value v), es') /\
        res = (case evaluate_builtin cx es'.accounts ann Keccak256 [expr_type e] [v] of
                 INL w => INL (Value w)
               | INR err => INR (Error err))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `materialise cx tv es1` >>
  Cases_on `?v. tv = Value v` >> gvs[] >>
  simp[materialise_def, return_def] >>
  simp[Once evaluate_def, return_def, lift_sum_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx es1.accounts ann Keccak256 [expr_type e] [v]` >>
  simp[return_def, raise_def] >> rw[] >> gvs[]
QED

Definition keccak256_tail_def:
  keccak256_tail ty x =
    if is_bytestring_type ty then compile_keccak256_bytes x
    else case ty of
      BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m
    | _ => compile_keccak256_word x
End

Theorem compile_expr_keccak256:
  !cenv ty ann e st.
    compile_expr cenv ty (Builtin ann Keccak256 [e]) st =
    compile_builtin_dispatch cenv ann ty Keccak256 [e] st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def)] >>
  Cases_on `e` >> simp[compile_expr_body_def, expr_size_def,
    list_size_def, expr_type_def]
QED

Theorem lower_value_keccak256:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Keccak256 [e]) sa =
      (op, sb) ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
      keccak256_tail (expr_type e) x s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_keccak256] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def, keccak256_tail_def] >>
  Cases_on `is_bytestring_type (expr_type e)` >> simp[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
  Cases_on `expr_type e` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED
