(* Typed source and actual execution of Abs, shared by expression simulations. *)
Theory exprSimAbsSource
Ancestors
  exprSimUnopProps exprSimWordBuiltins exprSimUnopComposeProps
  builtinProps freshWrites varsExt fragExec fragGasFresh venomExecSemantics
  vyperTypeSystem vyperTyping vyperValueOperation valueEncoding vyperValue
  vyperAST vyperInterpreter vyperState vyperContext compileEnv list words integer_word

Theorem word_abs_actual_run:
  compile_builtin_abs x sm = (dst,sn) /\ eval_operand x s = SOME w /\
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  (w <> INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
       eval_operand dst q = SOME (if word_msb w then 0w - w else w)) /\
  (w = INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = Abort Revert_abort q)
Proof
  strip_tac >>
  `straight_fresh (compile_builtin_abs x)` by simp[straight_fresh_abs] >>
  `writes_fresh sm (emitted_insts sm sn)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `eval_operand x (varsExt$drop_fresh sm s) = SOME w` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sm (varsExt$drop_fresh sm s)` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  drule_all compile_builtin_abs_run >> strip_tac >>
  `varsExt$vars_ext_result
    (run_inst_seq (emitted_insts sm sn) (varsExt$drop_fresh sm s))
    (run_inst_seq (emitted_insts sm sn) s)` by
    (irule varsExtTheory.run_inst_seq_vars_ext >>
     simp[varsExtTheory.vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  conj_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  Cases_on `run_inst_seq (emitted_insts sm sn) s` >>
  gvs[varsExtTheory.vars_ext_result_def, varsExtTheory.vars_ext_def] >>
  qpat_x_assum `_ = _ with vs_vars := _` SUBST1_TAC >>
  simp[varsExtTheory.eval_operand_vars_ext]
QED

Theorem word_abs_typed_source:
  value_has_type (BaseTV (IntT 256)) v ==>
  if typed_val_to_w256 (BaseTV (IntT 256)) v <> INT_MINw then
    ?v'. unop_result cx (BaseT (IntT 256)) Abs tys v es = INL v' /\
      typed_val_to_w256 (BaseTV (IntT 256)) v' =
        (if word_msb (typed_val_to_w256 (BaseTV (IntT 256)) v)
         then 0w - typed_val_to_w256 (BaseTV (IntT 256)) v
         else typed_val_to_w256 (BaseTV (IntT 256)) v)
  else ?m. unop_result cx (BaseT (IntT 256)) Abs tys v es =
    INR (Error (RuntimeError m))
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def] >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def, type_to_int_bound_def,
       bounded_int_op_def, typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = INT_MIN (:256)` >> gvs[]
QED

