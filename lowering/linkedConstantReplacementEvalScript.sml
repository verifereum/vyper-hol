(* Evaluate closed canonical constant replacements without reading state. *)
Theory linkedConstantReplacementEval
Ancestors
  vyperTypeContract vyperTypeConstantFold vyperTypeSystem vyperTypeEvalCaseProofs
  vyperTypeValues vyperInterpreter vyperState vyperValueOperation vyperContext
  vyperSubscriptOverlap vyperAST constSubst list pair option

Theorem eval_closed_constant_expr:
  constant_expr mods e /\ no_sha256_expr e /\
  vyperSubscriptOverlap$accesses_expr e = [] /\
  constant_value mods imms e = SOME v /\
  env.type_defs = type_env_all_modules mods /\ well_typed_expr env e /\
  get_tenv cx = type_env_all_modules mods ==>
  !st. eval_expr cx e st = (INL (Value v),st)
Proof
  `!x. accesses_expr x = [] ==> type_place_expr env x = NONE` by
    (ho_match_mp_tac
       (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
        SIMP_RULE (srw_ss()) []) >>
     simp[accesses_expr_def, Once well_typed_expr_def] >>
     rpt strip_tac >> simp[Once well_typed_expr_def]) >>
  `!kes. accesses_exprs (MAP SND kes) = accesses_named_exprs kes` by
    (Induct >> simp[accesses_expr_def] >> Cases >> simp[accesses_expr_def]) >>
  `(!mods imms e v.
     constant_value mods imms e = SOME v /\ constant_expr mods e /\
     accesses_expr e = [] /\ well_typed_expr env e /\
     env.type_defs = type_env_all_modules mods /\ get_tenv cx = type_env_all_modules mods ==>
     !st. eval_expr cx e st = (INL (Value v),st)) /\
   (!mods imms es vs.
     constant_values mods imms es = SOME vs /\ EVERY (constant_expr mods) es /\
     accesses_exprs es = [] /\ well_typed_exprs env es /\
     env.type_defs = type_env_all_modules mods /\ get_tenv cx = type_env_all_modules mods ==>
     !st. eval_exprs cx es st = (INL vs,st) /\
          LIST_REL (\e v. eval_expr cx e st = (INL (Value v),st)) es vs)` suffices_by
    (strip_tac >> strip_tac >>
     qpat_assum `!mods imms e v. constant_value _ _ _ = _ /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  ho_match_mp_tac constant_value_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`TopLevelName`] >-
    gvs[accesses_expr_def]
  >~ [`Literal`] >-
    gvs[constant_value_def, Once evaluate_def, return_def]
  >~ [`StructLit`] >-
    (gvs[constant_value_def, constant_expr_def, accesses_expr_def, AllCaseEqs()] >>
     `well_typed_exprs env (MAP SND kes)` by
       (irule well_typed_named_exprs_MAP_SND_stmt >> gvs[Once well_typed_expr_def]) >>
     `EVERY (constant_expr mods) (MAP SND kes)` by fs[EVERY_MEM] >>
     res_tac >>
     PairCases_on `v5` >> simp[Once evaluate_def, bind_def, return_def])
  >~ [`Subscript`] >-
    (`accesses_expr e = [] /\ accesses_expr e' = []` by gvs[accesses_expr_def] >>
     `type_place_expr env e = NONE` by res_tac >>
     `well_typed_expr env e /\ well_typed_expr env e'` by
       gvs[Once well_typed_expr_def] >>
     gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
     res_tac >> Cases_on `subscript_reads_base cx e e'` >>
     simp[Once evaluate_def, bind_def, return_def, read_result_def,
          select_result_def, lift_option_type_def, lift_sum_def])
  >~ [`Attribute`] >-
    (`accesses_expr e = [] /\ well_typed_expr env e` by
       gvs[accesses_expr_def, Once well_typed_expr_def] >>
     gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
     `well_formed_type env.type_defs (expr_type e)` by
       (Cases_on `e` >>
        gvs[accesses_expr_def, constant_expr_def, well_typed_expr_def, expr_type_def]) >>
     `!tv. evaluate_subscripts tv v' [AttrSubscript id] = INL v` by
       (gen_tac >> Cases_on `v'` >> gvs[evaluate_attribute_def, evaluate_subscripts_def, AllCaseEqs()]) >>
     gvs[well_formed_type_def, IS_SOME_EXISTS] >>
     simp[Once evaluate_def, bind_def, return_def, select_result_def,
          lift_option_type_def, lift_sum_def])
  >~ [`Builtin`] >-
    (`well_typed_exprs env es` by gvs[Once well_typed_expr_def] >>
     gvs[constant_value_def, constant_expr_def, accesses_expr_def, AllCaseEqs()] >>
     `EVERY (constant_expr mods) es` by fs[EVERY_MEM] >>
     `accesses_exprs es = []` by (Cases_on `risky_builtin bt` >> gvs[]) >>
     res_tac >>
     (all_tac >>~- ([`constant_length _ = SOME _`],
       `?arg. es = [arg]` by
         (Cases_on `es` >> fs[builtin_args_length_ok_def] >>
          Cases_on `t` >> fs[builtin_args_length_ok_def]) >>
       gvs[builtin_args_length_ok_def] >>
       `result_array_length cx (Value v') st = (INL n,st)` by
         (qspecl_then [`v'`,`n`,`cx`,`st`] mp_tac constant_length_result_array_length >> simp[]) >>
       simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
            return_def, builtin_args_length_ok_def])) >>
     `~is_self_codesize bt es /\ bt <> Env MsgGas /\ ~precompile_builtin bt` by
       (Cases_on `bt` >> gvs[is_self_codesize_def, constant_builtin_def, risky_builtin_def]) >>
     `code_slice_source bt es = NONE` by
       (Cases_on `code_slice_source bt es` >> simp[] >>
        rename1 `_ = SOME p` >> PairCases_on `p` >>
        gvs[code_slice_source_SOME, constant_builtin_def]) >>
     `evaluate_builtin cx st.accounts ty bt (MAP expr_type es) vs = INL v` by
       metis_tac[evaluate_builtin_constant_context] >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
          get_accounts_def, lift_sum_def, return_def])
  >~ [`TypeBuiltin`] >-
    (gvs[constant_value_def, constant_expr_def, accesses_expr_def, AllCaseEqs()] >>
     `well_typed_exprs env es` by gvs[Once well_typed_expr_def] >>
     `EVERY (constant_expr mods) es` by fs[EVERY_MEM] >>
     res_tac >>
     `evaluate_type_builtin cx tb typ (MAP expr_type es) vs = INL v` by
       metis_tac[evaluate_type_builtin_constant_context] >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, lift_sum_def])
  >~ [`constant_values _ _ []`] >-
    gvs[constant_value_def, Once evaluate_def, return_def] >>
  all_tac >>~- ([`constant_values _ _ (e::es)`],
    gvs[constant_value_def, well_typed_expr_def, accesses_expr_def, AllCaseEqs()] >>
    res_tac >> simp[Once evaluate_def, read_result_def, bind_def, return_def]) >>
  gvs[constant_value_def]
QED
