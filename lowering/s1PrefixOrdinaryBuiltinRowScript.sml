(* Ordinary builtins inherit prefix judgments from strictly smaller operands. *)
Theory s1PrefixOrdinaryBuiltinRow
Ancestors
  s1PrefixGuardedOrdinary s1PrefixCheckedContextFull
  s1PrefixBoolChainHeadMakeArray exprCallBounds s1PrefixPreds
  vyperAST vyperInterpreter vyperContext vyperState list

Theorem ordinary_builtin_size_row:
  !cx ann bt xs. bt <> NamedConst /\ (!p n. bt <> BoolChain p n) /\
    (!t n. bt <> MakeArray t n) /\
    (!a. expr_size a < expr_size (Builtin ann bt xs) ==> body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann bt xs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `?tops env s. body_const_cells_agree [(NONE,tops)] cx env s`)
  >- (once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `?tops env s. body_const_cells_agree _ _ _ _` strip_assume_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `!a. MEM a xs ==> body_expr_prefix_ok cx a` by
    (rpt strip_tac >>
     qpat_assum `!a. expr_size a < _ ==> _` irule >>
     drule expr_list_member_bound >> simp[expr_size_def]) >>
  `body_exprs_prefix_ok cx xs` by (irule prefix_list_from_members >> simp[]) >>
  `body_exprs_prefix_ok cx (TL xs)` by
    (irule prefix_list_from_members >> Cases_on `xs` >> fs[] >> metis_tac[]) >>
  irule body_builtin_ordinary_case_prefix >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule prefix_list_from_members >> simp[] >>
      qpat_assum `!a. expr_size a < _ ==> _` irule >>
      gvs[code_slice_source_SOME] >> simp[expr_size_def, list_size_def]) >>
  rpt strip_tac >> gvs[] >>
  `LENGTH xs = 1` by fs[type_check_def, assert_def, builtin_args_length_ok_def] >>
  gvs[LENGTH_EQ_1]
QED
