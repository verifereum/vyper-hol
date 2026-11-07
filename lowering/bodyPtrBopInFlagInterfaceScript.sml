Theory bodyPtrBopInFlagInterface
Ancestors bodyPtrBopInFlagCertificate exprBopFlag exprBopLowering exprLowering
  exprBopSimDefs exprSimDefs exprSimProps exprSimSource loweringSlice compileEnv vyperAST
  vyperValueOperation vyperValue vyperTyping vyperState valueEncoding

Theorem membership_flag_source_run:
  (bop = In \/ bop = NotIn) /\
  value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\ m <= 256 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) /\ fresh_vars_wrt sa s ==>
  ?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_flag_in_correct >> strip_tac >>
  qexistsl_tac [`BoolV (if bop = In then
    word_and (val_to_w256 v1) (val_to_w256 v2) <> 0w else
    word_and (val_to_w256 v1) (val_to_w256 v2) = 0w)`, `ss'`] >>
  simp[word_value_def, val_to_w256_def, venomExecSemanticsTheory.bool_to_word_def] >>
  reverse conj_tac
  >- (Cases_on `if bop = In then val_to_w256 v1 && val_to_w256 v2 <> 0w
        else val_to_w256 v1 && val_to_w256 v2 = 0w` >>
      simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  irule bop_result_flag_in >> simp[] >> qexists_tac `m` >> simp[]
QED

Theorem membership_flag_compile_dispatch:
  (bop = In \/ bop = NotIn) /\ expr_type e2 = FlagT fid ==>
  compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa =
    as_stack_val ann
      (comp_bind (lower_value compile_expr cenv (expr_type e1) e1) (\x.
       comp_bind (lower_value compile_expr cenv (expr_type e1) e2) (\y.
        compile_binop bop x y (expr_type e1)
          (if bop = Exp then expr_int_literal e1 else NONE)
          (if bop = Exp then expr_int_literal e2 else NONE))) sa)
Proof
  strip_tac >> simp[compile_expr_bop,
    Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
    compile_builtin_dispatch_body_def, lower_value_child_call] >>
  gvs[comp_bind_def, expr_type_def, ETA_AX] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem membership_flag_boundary_checks:
  evaluate_binop (Unsigned 0) (FlagTV 2) In (FlagV 0) (FlagV 3) =
    INL (BoolV F) /\
  evaluate_binop (Unsigned 0) (FlagTV 2) In (FlagV 1) (FlagV 2) =
    INL (BoolV F) /\
  evaluate_binop (Unsigned 0) (FlagTV 2) In (FlagV 1) (FlagV 3) =
    INL (BoolV T) /\
  evaluate_binop (Unsigned 0) (FlagTV 2) NotIn (FlagV 1) (FlagV 3) =
    INL (BoolV F)
Proof
  simp[evaluate_binop_def, binop_negate_def] >>
  simp[flag_and_zero] >> wordsLib.WORD_DECIDE_TAC
QED
