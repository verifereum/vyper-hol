(* The source's blueprint-offset test uses the same folded expression as
   the compiler when the expression contains no substituted constant name. *)
Theory createSizeBlueprintOffset
Ancestors
  exprBodyPreProps exprSimSource constSubstStmtsPreserve vyperCreate
  vyperPinFoldProps vyperTypeEvalProofs vyperTypeEvalSoundness
  bodyInvCodeProps exprSimHypsDefs constSubst supportedExprTraverse
  vyperAST vyperContext vyperInterpreter vyperOriginFold vyperState
  vyperTypeExprSoundness vyperTypeSystem vyperTyping vyperValue
  vyperValueOperation alist integer_word list words

Triviality blueprint_const_name_pred:
  cx_tops cx = tops ==>
  (\x. ?ty id. x = TopLevelName ty (NONE,id) /\
               IS_SOME (ALOOKUP (module_consts_env tops []) id)) =
  const_name_root cx
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >> Cases_on `x` >>
  gvs[const_name_root_def] >>
  rename1 `cx_const_name cx nsid` >> Cases_on `nsid` >>
  simp[cx_const_name_def, optionTheory.IS_SOME_EQ_NOT_NONE, ALOOKUP_NONE]
QED

Theorem create_blueprint_offset_bridge:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d) es /\
  args = target::value::((if hs then [salt] else []) ++ (off::ctors)) ==>
  (blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off)) /\
  (!oty i. origin_fold_value off = Literal oty (IntL i) ==>
     (!st. bind (eval_expr cx off) (read_result cx) st = (INL (IntV i), st)) /\
     dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32)))
Proof
  strip_tac >> drule body_inv_main_code >> strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  conj_tac
  >- (`subst_consts_expr (module_consts_env tops []) off = off` by
        (irule (cj 1 subst_consts_expr_unchanged) >>
         drule blueprint_const_name_pred >> disch_then SUBST1_TAC >>
         Cases_on `hs` >> gvs[supported_expr_exists_def]) >>
      Cases_on `hs` >> gvs[blueprint_literal_offset_def]) >>
  rpt gen_tac >> strip_tac >>
  `!st. bind (eval_expr cx off) (read_result cx) st = (INL (IntV i), st)` by
    (gen_tac >> drule origin_fold_value_literal_sound >>
     simp[bind_def, read_result_def, return_def, evaluate_literal_def]) >>
  conj_tac >- simp[] >>
  `well_typed_expr env off /\ expr_type off = BaseT (UintT 256)` by
    (Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  `call_evaluation_safe cx (int_calls_expr off)` by
    (drule_all body_inv_expr_body_pre_mods >>
     simp[expr_body_pre_mods_def] >> strip_tac >>
     drule create_call_evaluation_safe_args >> strip_tac >>
     irule call_evaluation_safe_exprs_mem >> qexists_tac `args` >>
     Cases_on `hs` >> gvs[]) >>
  `value_runtime_typed env (expr_type off) (IntV i)` by
    (qpat_x_assum `expr_type off = _` kall_tac >>
     qpat_assum `!st. bind _ _ st = _` (qspec_then `es` assume_tac) >>
     drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE[ETA_AX] eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >>
     gvs[expr_sim_inv_def]) >>
  gvs[value_runtime_typed_def, evaluate_type_def, value_has_type_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  simp[vyperValueTheory.dest_NumV_def, integer_wordTheory.i2w_def,
       wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED
