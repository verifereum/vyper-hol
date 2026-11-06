Theory augAssignPtrNumericProbe
Ancestors exprSimArith exprBopSimDefs exprLowering exprLoweringProps
  vyperValue valueEncoding loweringSlice list

(* This is the numerical premise of binop_frag_straight, not a lifted path. *)
Theorem checked_add_numeric_witness:
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 ==>
  (?v. bop_result cx ann Add tys (IntV i1) (IntV i2) es = INL v /\
       word_value v /\
       !x y sa sb op ss.
         compile_binop Add x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y ss = SOME (val_to_w256 (IntV i2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
             eval_operand op t = SOME (val_to_w256 v)) \/
  (?m. bop_result cx ann Add tys (IntV i1) (IntV i2) es =
         INR (Error (RuntimeError m)) /\
       !x y sa sb op ss.
         compile_binop Add x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y ss = SOME (val_to_w256 (IntV i2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t)
Proof
  strip_tac >>
  `bop_result cx ann Add tys (IntV i1) (IntV i2) es =
     if within_int_bound u (i1 + i2) then INL (IntV (i1 + i2))
     else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (qspecl_then [`cx`, `ann`, `Add`] (assume_tac o SRULE [LET_THM])
       bop_result_checked >> simp[]) >>
  Cases_on `within_int_bound u (i1 + i2)` >>
  simp[word_value_def, val_to_w256_def] >>
  rpt strip_tac >> gvs[compile_binop_def] >>
  drule_all compile_safe_add_run >> simp[]
QED
