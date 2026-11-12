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
  exprSimSliceSource exprSimSliceCompose exprSimSliceExtcode
  exprSimSliceOrdinary exprSimSliceExtcodeTyped
  exprSimDefs vyperState exprLoweringProps exprBopLowering

Theorem compile_slice_extcode_case[local]:
  slice_extcode_case nocalls ctx func cenv cx args /\
  is_extcode (HD args) /\ ~is_self_code (HD args) ==>
  expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  strip_tac >> rewrite_tac[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ann (Slice n) args)` by
    fs[expr_body_pre_def] >>
  drule slice_typed_args >>
  disch_then (qx_choose_then `src` (qx_choose_then `start` (qx_choose_then `len`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  gvs[] >>
  `?ct a. src = Builtin ct (Acc Code) [a]` by
    (qpat_x_assum `is_extcode src` mp_tac >>
     map_every (fn q => qpat_x_assum q kall_tac)
       [`expr_type src = _`, `slice_operands_ok _ _`] >>
     qid_spec_tac `src` >> recInduct is_extcode_ind >>
     simp[is_extcode_def]) >>
  gvs[] >>
  `well_typed_expr env (Builtin ct (Acc Code) [a])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)` mp_tac >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `!e. MEM e [start; len] ==> ~is_extcode e` by
    (gvs[vyperTypeSystemTheory.well_typed_expr_def] >> rpt strip_tac >>
     imp_res_tac exprSimSourceTheory.well_typed_extcode_type >> gvs[]) >>
  fs[Once vyperTypeSystemTheory.well_typed_expr_def,
     vyperTypeSystemTheory.well_typed_builtin_app_def,
     vyperTypeSystemTheory.account_item_type_def, vyperASTTheory.expr_type_def] >>
  `exprs_case nocalls ctx func cenv cx [start;len]` by
    fs[slice_extcode_case_def] >>
  `expr_sim_case nocalls ctx func cenv cx start` by fs[exprs_case_def] >>
  `expr_body_pre cenv cx env start es` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac
     >- fs[expr_body_pre_def] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env len es` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac
     >- fs[expr_body_pre_def] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env a es` by
    (irule slice_code_address_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >>
     fs[expr_body_pre_def]) >>
  irule slice_extcode_typed_entry >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `nocalls` >>
  fs[slice_extcode_case_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  metis_tac[]
QED

Theorem compile_slice_nonself_case:
  !nocalls ctx func cenv cx ann n args.
    ~is_self_code (HD args) /\
    (code_slice_source (Slice n) args = NONE ==>
     exprs_case nocalls ctx func cenv cx args) /\
    slice_extcode_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  rpt strip_tac >> Cases_on `is_extcode (HD args)`
  >- (irule compile_slice_extcode_case >> simp[]) >>
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
