(* Concrete semantic suffix runs, before pointer-path packaging. *)
Theory bodyPtrBopScalarRun
Ancestors exprSimArith exprSimBinopFrag exprBopSimDefs exprLowering
  freshWrites compileEnv valueEncoding vyperInterpreter loweringSlice
  vyperContext vyperValueOperation

Theorem bop_checked_fresh_run:
  MEM bop [Add; Sub; Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qabbrev_tac `rr = if bop = Add then i1 + i2 else
                      if bop = Sub then i1 - i2 else i1 * i2` >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es =
    if within_int_bound u rr then INL (IntV rr)
    else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (Cases_on `bop` >>
     gvs[Abbr `rr`, bop_result_def, evaluate_builtin_def,
         evaluate_binop_def, bounded_int_op_def] >> rw[]) >>
  asm_rewrite_tac[] >>
  `((within_int_bound u rr ==> ?t.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (i2w rr)) /\
    (~within_int_bound u rr ==> ?t.
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t))` by
    (gvs[Abbr `rr`, compile_binop_def]
     >- (drule_all compile_safe_add_run >> simp[])
     >- (drule_all compile_safe_sub_run >> simp[]) >>
     drule_all compile_safe_mul_run >> simp[]) >>
  Cases_on `within_int_bound u rr` >>
  gvs[word_value_def, val_to_w256_def] >> metis_tac[]
QED
