(*
 * Expression simulation: slice(b, start, length), including x.code and
 * self.code sources.
 *
 * compile_slice_case, the case lemma exprSimBuiltins re-exports for
 * compile_expr_sim (exprSimMain): from exprs_case of the operands and, for
 * an x.code source, slice_extcode_case, expr_vv_case of the builtin.
 *
 * slice(x.code, start, length) evaluates start and length before x.code,
 * and the lowering compiles x itself (EXTCODESIZE/EXTCODECOPY on it), so
 * the operands' exprs_case does not give a judgment for x.
 * slice_extcode_case gives the judgments in that evaluation order: those of
 * start and length, and, when they evaluate, those of x.
 *
 * The self.code source is exprSimSliceSelfCode's named residual
 * compile_slice_self_code_case; compile_slice_nonself_case covers the rest.
 *)

Theory exprSimSlice
Ancestors
  exprSimSliceSelfCode exprSimHyps exprSimHypsDefs exprLowering vyperAST
  exprSimSliceSource exprSimSliceCompose exprSimSliceOrdinary
  exprSimDefs vyperState exprLoweringProps exprBopLowering

Theorem compile_slice_nonself_case:
  !nocalls ctx func cenv cx ann n args.
    ~is_self_code (HD args) /\
    (code_slice_source (Slice n) args = NONE ==>
     exprs_case nocalls ctx func cenv cx args) /\
    slice_extcode_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  rpt strip_tac >> Cases_on `is_extcode (HD args)`
  >- ((* PORT_ADMISSION: SEQ-1248, bot/opus/seq-1248-t16-pin, built at c66a72744 *)
      cheat) >>
  irule compile_slice_ordinary_case >> simp[] >>
  first_x_assum irule >>
  Cases_on `code_slice_source (Slice n) args` >> simp[] >>
  PairCases_on `x` >>
  gvs[vyperInterpreterTheory.code_slice_source_SOME, is_extcode_def]
QED

(* An operand list below the induction's size bound meets slice_extcode_case:
   the code address is a smaller expression than the operand list. *)
Theorem slice_extcode_case_below:
  !cenv args ctx func cx.
    expr_sim_below cenv (list_size expr_size args) ==>
    slice_extcode_case T ctx func cenv cx args
Proof
  rw[slice_extcode_case_def]
  >- (irule exprs_case_below >> irule expr_sim_below_mono >>
      first_assum (irule_at Any) >>
      simp[listTheory.list_size_def]) >>
  `expr_ok cenv a` suffices_by simp[expr_ok_case] >>
  gvs[expr_sim_below_def] >> first_x_assum irule >>
  simp[listTheory.list_size_def, vyperASTTheory.expr_size_def]
QED

Theorem compile_slice_case:
  !nocalls ctx func cenv cx ann n args.
    (code_slice_source (Slice n) args = NONE ==>
     exprs_case nocalls ctx func cenv cx args) /\
    slice_extcode_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  rpt strip_tac >> Cases_on `is_self_code (HD args)`
  >- (irule compile_slice_self_code_case >> simp[]) >>
  irule compile_slice_nonself_case >> simp[]
QED
