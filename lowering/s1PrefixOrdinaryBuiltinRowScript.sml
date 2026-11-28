(* Ordinary builtins inherit prefix judgments from strictly smaller operands. *)
Theory s1PrefixOrdinaryBuiltinRow
Ancestors
  s1PrefixGuardedOrdinary s1PrefixCheckedContextFull
  s1PrefixBoolChainHeadMakeArray exprCallBounds s1PrefixPreds
  vyperAST vyperInterpreter vyperContext vyperState list alist
  s1PrefixSyntaxCalls vyperTypeCallGraph

Theorem ordinary_builtin_size_row:
  !cx ann bt xs. bt <> NamedConst /\ (!p n. bt <> BoolChain p n) /\
    (!t n. bt <> MakeArray t n) /\
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ann bt xs))) /\
    (!a. expr_size a < expr_size (Builtin ann bt xs) /\
        (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann bt xs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `?tops env s. body_const_cells_agree [(NONE,tops)] cx env s`)
  >- (once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `?tops env s. body_const_cells_agree _ _ _ _` strip_assume_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
  `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
     (int_calls_exprs xs)` by (res_tac >> fs[int_calls_expr_def]) >>
  `!a. MEM a xs ==> body_expr_prefix_ok cx a` by
    (rpt strip_tac >>
     qpat_assum `!a. expr_size a < _ /\ _ ==> _` irule >>
     rpt conj_tac
     >- (rpt strip_tac >> gvs[int_calls_exprs_members] >> metis_tac[]) >>
     drule expr_list_member_bound >> simp[expr_size_def]) >>
  `body_exprs_prefix_ok cx xs` by (irule prefix_list_from_members >> simp[]) >>
  `body_exprs_prefix_ok cx (TL xs)` by
    (irule prefix_list_from_members >> Cases_on `xs` >> fs[] >> metis_tac[]) >>
  `body_exprs_full_ok cx xs /\ body_exprs_full_ok cx (TL xs)` by
    (conj_tac >>
     qpat_assum `!ys. EVERY _ _ ==> body_exprs_full_ok cx ys` irule >>
     Cases_on `xs` >> fs[int_calls_expr_def, EVERY_APPEND]) >>
  irule body_builtin_ordinary_case_prefix >>
  simp[] >> rpt conj_tac >> rpt strip_tac >>
  TRY (qpat_assum `!x. EVERY _ _ ==> body_expr_full_ok cx x` irule) >>
  TRY (qpat_assum `!ys. EVERY _ _ ==> body_exprs_full_ok cx ys` irule) >>
  TRY (irule prefix_list_from_members >> simp[] >> rpt strip_tac >>
       qpat_assum `!a. expr_size a < _ /\ _ ==> _` irule) >>
  TRY (qpat_x_assum `code_slice_source bt xs = SOME _` mp_tac >>
       simp[optionTheory.SOME_11, pairTheory.FORALL_PROD] >>
       Cases_on `v` >> simp[code_slice_source_SOME] >> rpt strip_tac >>
       gvs[int_calls_expr_def, EVERY_APPEND, expr_size_def, list_size_def] >> NO_TAC) >>
  TRY (qpat_x_assum `code_slice_source bt xs = SOME (_,addr)` mp_tac >>
       simp[code_slice_source_SOME] >> rpt strip_tac >>
       gvs[int_calls_expr_def, EVERY_APPEND, expr_size_def, list_size_def] >> NO_TAC) >>
  `LENGTH xs = 1` by fs[type_check_def, assert_def, builtin_args_length_ok_def] >>
  gvs[LENGTH_EQ_1, int_calls_expr_def, EVERY_APPEND] >> metis_tac[]
QED
