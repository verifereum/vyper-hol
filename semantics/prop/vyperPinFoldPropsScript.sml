Theory vyperPinFoldProps
Ancestors
  vyperPinFold vyperConstEval vyperEvalPureExpr vyperContext vyperState vyperValue vyperAST
  vyperValueOperation vyperTypeExprSoundness

Theorem pin_constant_literal_evaluate:
  pin_constant_literal v = SOME l ==> evaluate_literal l = v
Proof
  Cases_on `v` >> rw[pin_constant_literal_def, constant_literal_def] >>
  simp[evaluate_literal_def]
QED

Theorem evaluate_builtin_pin_closed[local]:
  pin_foldable_builtin b /\ EVERY (\t. ?bt. t = BaseT bt) tys ==>
  evaluate_builtin cx acc (BaseT bt) b tys vs =
  evaluate_builtin empty_evaluation_context empty_accounts (BaseT bt) b tys vs
Proof
  Cases_on `b` >> rw[pin_foldable_builtin_def] >>
  simp[evaluate_builtin_def, evaluate_type_def] >>
  Cases_on `tys` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[evaluate_type_def]
QED

Theorem pin_literal_values_pure:
  pin_literal_values es = SOME vs ==>
  eval_pure_exprs cx st es = SOME vs
Proof
  qid_spec_tac `vs` >> Induct_on `es` >>
  simp[pin_literal_values_def, eval_pure_expr_def] >>
  Cases_on `h` >> simp[pin_literal_values_def] >>
  rw[AllCaseEqs()] >>
  gvs[eval_pure_expr_def, read_result_def, return_def]
QED

Theorem evaluate_type_empty_context[local]:
  evaluate_type FEMPTY ty = SOME tv ==>
  evaluate_type tenv ty = SOME tv
Proof
  qid_spec_tac `tenv` >> ho_match_mp_tac finite_mapTheory.fmap_INDUCT >>
  simp[] >> rpt strip_tac >>
  irule (cj 1 evaluate_type_mono) >>
  qexists_tac `x` >> simp[finite_mapTheory.DOMSUB_FUPDATE_THM,
    finite_mapTheory.DOMSUB_NOT_IN_DOM]
QED

Theorem pin_literal_tree_pure_mutual[local]:
  (!t. pin_literal_tree t ==>
       ?v. eval_pure_expr cx st t = SOME (Value v)) /\
  (!ts. pin_literal_trees ts ==>
        ?vs. eval_pure_exprs cx st ts = SOME vs)
Proof
  ho_match_mp_tac pin_literal_tree_ind >>
  simp[pin_literal_tree_def, eval_pure_expr_def] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[optionTheory.IS_SOME_EXISTS] >>
      drule evaluate_type_empty_context >>
      disch_then (qspec_then `get_tenv cx` assume_tac) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      simp[builtin_args_length_ok_def, evaluate_builtin_def]) >>
  rpt strip_tac >>
  gvs[eval_pure_expr_def, read_result_def, return_def]
QED

Theorem pin_literal_tree_pure:
  pin_literal_tree t ==> ?v. eval_pure_expr cx st t = SOME (Value v)
Proof
  metis_tac[pin_literal_tree_pure_mutual]
QED

Theorem pin_literal_trees_pure:
  pin_literal_trees ts ==> ?vs. eval_pure_exprs cx st ts = SOME vs
Proof
  metis_tac[pin_literal_tree_pure_mutual]
QED

Theorem pin_literal_trees_pure_EL[local]:
  !es vs n. pin_literal_trees es /\
    eval_pure_exprs cx st es = SOME vs /\ n < LENGTH es ==>
    LENGTH vs = LENGTH es /\
    eval_pure_expr cx st (EL n es) = SOME (Value (EL n vs))
Proof
  Induct >> simp[pin_literal_tree_def, eval_pure_expr_def] >>
  rpt gen_tac >> strip_tac >>
  drule pin_literal_tree_pure >>
  disch_then (qspecl_then [`st`, `cx`] strip_assume_tac) >>
  gvs[read_result_def, return_def, AllCaseEqs()] >>
  `LENGTH vs' = LENGTH es` by
    metis_tac[cj 2 eval_pure_to_eval_mutual,
      vyperInterpreterTheory.eval_exprs_length] >>
  Cases_on `n` >> gvs[]
QED

Theorem pin_literal_tree_subscript_pure:
  pin_literal_tree (Builtin (ArrayT elem bd) (MakeArray (SOME elem) bd) es) /\
  0 <= i /\ Num i < LENGTH es /\
  expr_type src = ArrayT elem bd /\
  eval_pure_expr cx st
    (Builtin (ArrayT elem bd) (MakeArray (SOME elem) bd) es) =
      SOME (Value av) /\
  eval_pure_expr cx st src = SOME (Value av) /\
  eval_pure_expr cx st index = SOME (Value (IntV i)) /\
  eval_pure_expr cx st (EL (Num i) es) = SOME (Value v) ==>
  eval_pure_expr cx st (Subscript ty src index) = SOME (Value v)
Proof
  strip_tac >>
  gvs[pin_literal_tree_def, optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_empty_context >>
  disch_then (qspec_then `get_tenv cx` assume_tac) >>
  drule pin_literal_trees_pure >>
  disch_then (qspecl_then [`st`, `cx`] strip_assume_tac) >>
  drule_all pin_literal_trees_pure_EL >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  gvs[eval_pure_expr_def, builtin_args_length_ok_def,
      evaluate_builtin_def] >>
  Cases_on `subscript_reads_base cx src index` >>
  simp[read_result_def, return_def, select_result_def,
       evaluate_type_def, bind_def, lift_option_type_def, lift_sum_def,
       evaluate_subscripts_def] >>
  Cases_on `bd` >>
  gvs[make_array_value_def, array_index_def, compatible_bound_def,
      enumerate_static_array_ALOOKUP, return_def, listTheory.oEL_THM] >>
  qspecl_then [`default_value tv`, `0`, `vs`, `Num i`]
    mp_tac enumerate_static_array_ALOOKUP >>
  simp[] >> disch_then SUBST1_TAC >>
  Cases_on `EL (Num i) vs = default_value tv` >> gvs[return_def]
QED

Theorem pin_fold_builtin_literal_pure:
  pin_fold_builtin ty b fs = Literal rt l /\
  MAP expr_type es = MAP expr_type fs /\
  (!vs. pin_literal_values fs = SOME vs ==>
        eval_pure_exprs cx st es = SOME vs) ==>
  eval_pure_expr cx st (Builtin ty b es) =
    SOME (Value (evaluate_literal l))
Proof
  Cases_on `ty` >> simp[pin_fold_builtin_def] >>
  Cases_on `b = Len`
  >- (gvs[] >> Cases_on `fs` >> simp[pin_foldable_builtin_def] >>
      Cases_on `t` >> simp[pin_foldable_builtin_def] >>
      Cases_on `h` >> simp[pin_foldable_builtin_def] >>
      rename1 `Literal _ lit` >> Cases_on `lit` >>
      simp[pin_foldable_builtin_def] >> rpt strip_tac >>
      gvs[pin_literal_values_def, evaluate_literal_def,
          eval_pure_expr_def, AllCaseEqs()] >>
      Cases_on `tv` >>
      gvs[read_result_def, return_def, raise_def] >>
      simp[result_array_length_def, read_result_def, return_def, bind_def] >>
      Cases_on `p` >>
      simp[result_array_length_def, read_result_def, bind_def,
           return_def] >>
      Cases_on `t'` >>
      gvs[result_array_length_def, read_result_def, bind_def, return_def] >>
      Cases_on `b'` >>
      gvs[read_place_def, read_storage_slot_def, bind_def, lift_option_def,
          vyperStorageTheory.decode_value_def,
          return_def, raise_def, AllCaseEqs()] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
  Cases_on `b` >> gvs[pin_foldable_builtin_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), pin_fold_result_def] >>
  drule pin_constant_literal_evaluate >> strip_tac >>
  gvs[builtin_args_length_ok_def, pin_literal_values_def] >>
  qmatch_goalsub_abbrev_tac `Builtin out op args` >>
  `EVERY (\t. ?bt. t = BaseT bt) (MAP expr_type args)` by
    (simp[Abbr `args`] >> gvs[listTheory.EVERY_MAP, combinTheory.o_DEF] >>
     metis_tac[]) >>
  imp_res_tac evaluate_builtin_pin_closed >>
  unabbrev_all_tac >>
  gvs[eval_pure_expr_def, pin_foldable_builtin_def,
      builtin_args_length_ok_def] >>
  qpat_x_assum `MAP expr_type es = _` (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
  simp[]
QED

Theorem pin_fold_type_builtin_literal_pure:
  pin_fold_expr (TypeBuiltin ty tb typ []) = Literal rt l ==>
  eval_pure_expr cx st (TypeBuiltin ty tb typ []) =
    SOME (Value (evaluate_literal l))
Proof
  Cases_on `ty` >> Cases_on `tb` >>
  simp[pin_fold_expr_def, pin_fold_result_def, AllCaseEqs()] >>
  rpt strip_tac >> drule pin_constant_literal_evaluate >> strip_tac >>
  gvs[eval_pure_expr_def, type_builtin_args_length_ok_def,
      evaluate_type_builtin_def]
QED

Theorem pin_fold_builtin_cases[local]:
  !ty b fs. pin_fold_builtin ty b fs = Builtin ty b fs \/
  ?rt l. pin_fold_builtin ty b fs = Literal rt l
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[pin_fold_builtin_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[pin_fold_result_def])
QED

Theorem pin_fold_exprs_types[local]:
  MAP expr_type (pin_fold_exprs es) = MAP expr_type es
Proof
  Induct_on `es` >> simp[pin_fold_expr_def]
QED

Theorem pin_fold_exprs_length[local]:
  LENGTH (pin_fold_exprs es) = LENGTH es
Proof
  Induct_on `es` >> simp[pin_fold_expr_def]
QED

Theorem pin_literal_values_trees[local]:
  !es vs. pin_literal_values es = SOME vs ==> pin_literal_trees es
Proof
  Induct >> simp[pin_literal_values_def, pin_literal_tree_def] >>
  Cases_on `h` >> simp[pin_literal_values_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), pin_literal_tree_def] >>
  metis_tac[]
QED

Theorem pin_fold_type_builtin_tree_pure[local]:
  pin_literal_tree (pin_fold_expr (TypeBuiltin ty tb typ [])) ==>
  ?v. eval_pure_expr cx st (TypeBuiltin ty tb typ []) = SOME (Value v) /\
      eval_pure_expr cx st (pin_fold_expr (TypeBuiltin ty tb typ [])) =
        SOME (Value v)
Proof
  strip_tac >>
  `?rt l. pin_fold_expr (TypeBuiltin ty tb typ []) = Literal rt l`
    suffices_by
      (rpt strip_tac >> drule pin_fold_type_builtin_literal_pure >>
       disch_then (qspecl_then [`st`, `cx`] assume_tac) >>
       gvs[eval_pure_expr_def]) >>
  Cases_on `ty` >> Cases_on `tb` >>
  gvs[pin_fold_expr_def, pin_fold_result_def, pin_literal_tree_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[pin_literal_tree_def])
QED

Theorem pin_fold_expr_tree_pure_mutual[local]:
  (!e. pin_literal_tree (pin_fold_expr e) ==>
    ?v. eval_pure_expr cx st e = SOME (Value v) /\
        eval_pure_expr cx st (pin_fold_expr e) = SOME (Value v)) /\
  (!es. pin_literal_trees (pin_fold_exprs es) ==>
    eval_pure_exprs cx st es = eval_pure_exprs cx st (pin_fold_exprs es))
Proof
  ho_match_mp_tac pin_fold_expr_ind >>
  rpt conj_tac >> rpt gen_tac
  >- (simp[pin_fold_expr_def] >> rpt strip_tac >>
      qspecl_then [`ty`, `b`, `pin_fold_exprs es`]
        strip_assume_tac pin_fold_builtin_cases
      >- (gvs[] >> drule pin_literal_tree_pure >>
          disch_then (qspecl_then [`st`, `cx`] strip_assume_tac) >>
          Cases_on `b` >> gvs[pin_literal_tree_def] >>
          Cases_on `o'` >> gvs[pin_literal_tree_def] >>
          gvs[eval_pure_expr_def, builtin_args_length_ok_def,
              pin_fold_exprs_types, pin_fold_exprs_length]) >>
      gvs[pin_literal_tree_def] >>
      qexists_tac `evaluate_literal l` >>
      reverse conj_tac >- simp[eval_pure_expr_def] >>
      irule pin_fold_builtin_literal_pure >>
      qexists_tac `pin_fold_exprs es` >>
      simp[pin_fold_exprs_types] >>
      metis_tac[pin_literal_values_trees, pin_literal_values_pure])
  >- metis_tac[pin_fold_type_builtin_tree_pure]
  >- metis_tac[pin_fold_type_builtin_tree_pure]
  >- metis_tac[pin_fold_type_builtin_tree_pure]
  >- (simp[pin_fold_expr_def] >> rpt strip_tac >>
      Cases_on `pin_fold_expr e` >>
      gvs[pin_fold_subscript_def, pin_literal_tree_def] >>
      rename1 `Builtin aty b fs` >> Cases_on `b` >>
      gvs[pin_fold_subscript_def, pin_literal_tree_def] >>
      Cases_on `o'` >> gvs[pin_fold_subscript_def, pin_literal_tree_def] >>
      Cases_on `pin_fold_expr e'` >>
      gvs[pin_fold_subscript_def, pin_literal_tree_def] >>
      rename1 `Literal ity lit` >> Cases_on `lit` >>
      gvs[pin_fold_subscript_def, pin_literal_tree_def] >>
      IF_CASES_TAC >> gvs[pin_literal_tree_def] >>
      drule pin_literal_tree_pure >>
      disch_then (qspecl_then [`st`, `cx`] strip_assume_tac) >>
      rename1 `eval_pure_expr cx st (EL (Num i) fs) = SOME (Value selected)` >>
      qexists_tac `selected` >> reverse conj_tac >- simp[] >>
      irule pin_literal_tree_subscript_pure >>
      `expr_type e = ArrayT ty b'` by
        metis_tac[pin_fold_expr_type, expr_type_def] >>
      gvs[eval_pure_expr_def, evaluate_literal_def, pin_literal_tree_def] >>
      metis_tac[]) >>
  simp[pin_fold_expr_def, pin_literal_tree_def, eval_pure_expr_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem pin_fold_expr_tree_pure:
  pin_literal_tree (pin_fold_expr e) ==>
  ?v. eval_pure_expr cx st e = SOME (Value v) /\
      eval_pure_expr cx st (pin_fold_expr e) = SOME (Value v)
Proof
  metis_tac[pin_fold_expr_tree_pure_mutual]
QED

(* Only a literal result replaces the original expression in consumers.
   A nonliteral normal form is used solely to classify provenance. *)
Theorem pin_fold_expr_literal_sound:
  pin_fold_expr e = Literal ty l ==>
  eval_expr cx e st = (INL (Value (evaluate_literal l)), st)
Proof
  strip_tac >>
  `pin_literal_tree (pin_fold_expr e)` by simp[pin_literal_tree_def] >>
  drule pin_fold_expr_tree_pure >>
  disch_then (qspecl_then [`st`, `cx`] strip_assume_tac) >>
  gvs[eval_pure_expr_def] >>
  irule eval_pure_expr_to_eval_expr_some >> simp[]
QED
