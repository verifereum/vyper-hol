(* ECRecover boundaries for the counted memory proof.
   The ecrecover-specific lemmas below restate the local lemmas of the same
   names in exprSimPrecompilesScript.sml; their proofs are from the S1 base.
   That theory is outside the task's permitted local-export exception. *)
Theory bodyMemBiECRecoverFacts
Ancestors
  exprSimPrecompiles exprSimDefs exprSimProps exprLowering
  exprLoweringProps exprSimWordArgs exprSimHypsDefs
  vyperTyping vyperAST vyperTypeSystem compileEnv list rich_list
  builtinMisc loweringPosts exprBopLowering vyperInterpreter vyperState
  vyperContext vyperValue vyperTypeInvariants valueEncoding
  integer_word words byte
Libs
  monadsyntax

Theorem ecrecover_typing:
  well_typed_builtin_app ty ECRecover ts ==>
  LENGTH ts = 4 /\ ty = BaseT AddressT /\
  HD ts = BaseT (BytesT (Fixed 32)) /\
  (EL 1 ts = BaseT (UintT 8) \/ EL 1 ts = BaseT (UintT 256) \/
   EL 1 ts = BaseT (BytesT (Fixed 32))) /\
  EVERY (\t. t = BaseT (UintT 256) \/ t = BaseT (BytesT (Fixed 32))) (TL (TL ts))
Proof
  simp[well_typed_builtin_app_def]
QED

Theorem ecrecover_pre_types:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es ==>
  ann = BaseT AddressT /\ LENGTH args = 4 /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  drule ecrecover_typing >> simp[] >> strip_tac >>
  `LENGTH args = 4` by simp[] >>
  gvs[LENGTH_EQ_NUM_compute] >> gvs[is_word_type_def]
QED

Theorem lower_value_ecrecover:
  lower_value compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa = (op,sb) ==>
  ?h v r sig sm. lower_word_args cenv (\e. ty) [a;b;c;d] sa = ([h;v;r;sig],sm) /\
    compile_ecrecover h v r sig sm = (op,sb)
Proof
  strip_tac >>
  `compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa =
    compile_builtin_dispatch cenv ann ty ECRecover [a;b;c;d] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def] >>
     Cases_on `c` >> simp[names_builtin_def]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  goal_assum (drule_at Any) >>
  simp[lower_word_args_def, comp_bind_def, comp_return_def]
QED

Theorem lower_value_ecrecover_args:
  LENGTH args = 4 /\
  lower_value compile_expr cenv ty (Builtin ann ECRecover args) sa = (op,sb) ==>
  ?h v r sig sm. lower_word_args cenv (\e. ty) args sa = ([h;v;r;sig],sm) /\
    compile_ecrecover h v r sig sm = (op,sb)
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  drule lower_value_ecrecover >> simp[]
QED

Theorem compile_ecrecover_stack:
  LENGTH args = 4 /\
  compile_expr cenv ty (Builtin ann ECRecover args) sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `Builtin ann ECRecover [a;b;c;d]` >>
  `compile_expr cenv ty (Builtin ann ECRecover [a;b;c;d]) sa =
    compile_builtin_dispatch cenv ann ty ECRecover [a;b;c;d] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def] >>
     Cases_on `c` >> simp[names_builtin_def]) >>
  gvs[] >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[as_stack_val_pair]
QED

Theorem ecrecover_source_outcome_step:
  precompile_call_success ECRecover es =
    case es.outcomes of
      NONE => (INL (),es)
    | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
    | SOME (outcome::rest) =>
        (if call_outcome_success outcome then INL ()
         else INR (Error (RuntimeError "precompile failed")),
         es with outcomes := SOME rest)
Proof
  Cases_on `es.outcomes` >> simp[precompile_call_success_def, return_def] >>
  rename1 `SOME os` >> Cases_on `os` >>
  simp[check_def, assert_def, return_def, raise_def] >>
  Cases_on `call_outcome_success h` >> simp[return_def, raise_def]
QED

Theorem ecrecover_arg_typed_encoding:
  ((?k. tv = BaseTV (UintT k) /\ k <= 256) \/
   tv = BaseTV (BytesT (Fixed 32))) /\ value_has_type tv x ==>
  ecrecover_arg_to_num x = SOME (w2n (typed_val_to_w256 tv x))
Proof
  strip_tac
  >- (Cases_on `x` >>
      gvs[value_has_type_def, ecrecover_arg_to_num_def,
          typed_val_to_w256_def, val_to_w256_def] >>
      `Num i < 2 ** 256` by
        (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >>
         simp[]) >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      gvs[i2w_def, dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  Cases_on `x` >>
  gvs[value_has_type_def, ecrecover_arg_to_num_def,
      typed_val_to_w256_def, PAD_LEFT, PAD_RIGHT]
QED

Theorem evaluate_ecrecover_encoded:
  LENGTH bs = 32 /\
  ecrecover_arg_to_num va = SOME v /\
  ecrecover_arg_to_num ra = SOME r /\
  ecrecover_arg_to_num sa = SOME s ==>
  evaluate_ecrecover [BytesV bs;va;ra;sa] =
    INL (AddressV (case vfmExecution$ecrecover
      (word_of_bytes_be bs) v r s of NONE => 0w | SOME addr => addr))
Proof
  strip_tac >>
  Cases_on `vfmExecution$ecrecover (word_of_bytes_be bs) v r s` >>
  simp[evaluate_ecrecover_def]
QED

Theorem evaluate_ecrecover_typed:
  value_has_type (BaseTV (BytesT (Fixed 32))) vh /\
  EVERY (\tv. (?k. tv = BaseTV (UintT k) /\ k <= 256) \/
                tv = BaseTV (BytesT (Fixed 32))) [tv;tr;ts] /\
  value_has_type tv va /\ value_has_type tr ra /\ value_has_type ts sa ==>
  evaluate_ecrecover [vh;va;ra;sa] =
    INL (AddressV (case vfmExecution$ecrecover
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh)
      (w2n (typed_val_to_w256 tv va))
      (w2n (typed_val_to_w256 tr ra))
      (w2n (typed_val_to_w256 ts sa)) of NONE => 0w | SOME addr => addr))
Proof
  strip_tac >>
  `ecrecover_arg_to_num va = SOME (w2n (typed_val_to_w256 tv va))` by
    (irule ecrecover_arg_typed_encoding >> gvs[]) >>
  `ecrecover_arg_to_num ra = SOME (w2n (typed_val_to_w256 tr ra))` by
    (irule ecrecover_arg_typed_encoding >> gvs[]) >>
  `ecrecover_arg_to_num sa = SOME (w2n (typed_val_to_w256 ts sa))` by
    (irule ecrecover_arg_typed_encoding >> gvs[]) >>
  qpat_x_assum `value_has_type (BaseTV (BytesT (Fixed 32))) vh` mp_tac >>
  Cases_on `vh` >> simp[value_has_type_def] >> strip_tac >>
  simp[typed_val_to_w256_def, PAD_LEFT, PAD_RIGHT] >>
  irule evaluate_ecrecover_encoded >> simp[]
QED

Theorem ecrecover_typed_result:
  well_typed_builtin_app ann ECRecover (MAP expr_type args) /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs ==>
  ?ah av ar asig vh va ra sa tv tr ts.
    args = [ah;av;ar;asig] /\ vs = [vh;va;ra;sa] /\
    evaluate_type (get_tenv cx) (expr_type ah) = SOME (BaseTV (BytesT (Fixed 32))) /\
    evaluate_type (get_tenv cx) (expr_type av) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type ar) = SOME tr /\
    evaluate_type (get_tenv cx) (expr_type asig) = SOME ts /\
    builtin_result cx acc ann ECRecover (MAP expr_type args) vs =
      INL (AddressV (case vfmExecution$ecrecover
        (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh)
        (w2n (typed_val_to_w256 tv va))
        (w2n (typed_val_to_w256 tr ra))
        (w2n (typed_val_to_w256 ts sa)) of NONE => 0w | SOME addr => addr))
Proof
  strip_tac >> drule ecrecover_typing >> simp[] >> strip_tac >>
  `LENGTH args = 4` by simp[] >>
  `LENGTH vs = 4` by metis_tac[LIST_REL_LENGTH] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  simp[builtin_result_def, evaluate_builtin_def] >>
  qmatch_goalsub_rename_tac `evaluate_ecrecover [vh;va;ra;sa]` >>
  qmatch_goalsub_abbrev_tac `AddressV addr` >>
  `evaluate_ecrecover [vh;va;ra;sa] = INL (AddressV addr)` suffices_by simp[] >>
  simp[Abbr `addr`] >> irule evaluate_ecrecover_typed >> simp[]
QED

Theorem ecrecover_read_cases:
  LENGTH args = 4 /\
  (do r <- eval_expr cx (Builtin ann ECRecover args); read_result cx r od) es = (res,es') ==>
  (?exc. eval_exprs cx args es = (INR exc,es') /\ res = INR exc) \/
  ?vs es1. eval_exprs cx args es = (INL vs,es1) /\
    (case builtin_result cx es1.accounts ann ECRecover (MAP expr_type args) vs of
       INR exc => res = INR exc /\ es' = es1
     | INL w => (do precompile_call_success ECRecover; return w od) es1 = (res,es'))
Proof
  strip_tac >> qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr,es1)` >> Cases_on `rr` >>
  simp[get_accounts_def, bind_def, return_def, lift_sum_def, builtin_result_def] >>
  rename1 `evaluate_builtin cx _ ann ECRecover _ vs` >>
  Cases_on `evaluate_builtin cx es1.accounts ann ECRecover (MAP expr_type args) vs` >>
  simp[bind_def, return_def, raise_def, read_result_def, ignore_bind_def] >>
  Cases_on `precompile_call_success ECRecover es1` >>
  rename1 `precompile_call_success ECRecover es1 = (out,es2)` >> Cases_on `out` >>
  simp[bind_def, return_def, read_result_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem eval_expr_ecrecover_read_action:
  LENGTH args = 4 ==>
  bind (eval_expr cx (Builtin ann ECRecover args)) (read_result cx) =
  bind (eval_exprs cx args)
    (\vs ee. case builtin_result cx ee.accounts ann ECRecover (MAP expr_type args) vs of
       INR exc => (INR exc, ee)
     | INL w => (do precompile_call_success ECRecover; return w od) ee)
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (Builtin ann ECRecover args)) (read_result cx) x` >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) ecrecover_read_cases) >>
  strip_tac >> gvs[bind_def] >>
  Cases_on `builtin_result cx es1.accounts ann ECRecover (MAP expr_type args) vs` >>
  gvs[]
QED
