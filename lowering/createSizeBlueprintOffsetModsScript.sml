(* Apply the shared literal-offset rules to the operand of a blueprint call. *)
Theory createSizeBlueprintOffsetMods
Ancestors
  createSizeBlueprintOffset createExprSizeExitDefsMods
  createSizeBlueprintOffsetElabMods bodyInvSplit bodySimStmtFacts exprSimSend
  valueEncoding valueLoadProps vyperTypeExprSoundness
  alist constSubstModsCorrect blueprintLiteralOffsetProps createSizeOperandPreMods exprBodyPreProps
  exprLowering exprSimHypsDefs integer_word list vyperAST vyperCreate
  vyperInterpreter vyperOriginFold vyperPinFold vyperState vyperTypeSystem vyperValue words

Theorem blueprint_offset_literal_bit_mods:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALL_DISTINCT (MAP FST mods) /\
  expr_body_pre_mods mods cenv cx env offset es /\
  LENGTH salts = (if salted then 1 else 0) ==>
  blueprint_literal_offset cx salted (target::amount::(salts ++ offset::ctor)) =
    IS_SOME (expr_int_literal (origin_fold_value offset))
Proof
  strip_tac >>
  `subst_consts_expr_mods (consts_env_mods mods) offset = offset` by
    (irule blueprint_offset_subst_unchanged_mods >> simp[] >>
     fs[expr_body_pre_mods_def]) >>
  Cases_on `salted` >> gvs[blueprint_literal_offset_def, LENGTH_EQ_NUM_compute,
    blueprint_offset_form]
QED

Theorem create_blueprint_offset_bridge_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env
    (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d) es /\
  args = target::value::((if hs then [salt] else []) ++ (off::ctors)) ==>
  (blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off)) /\
  (!oty i. origin_fold_value off = Literal oty (IntL i) ==>
     (!st. bind (eval_expr cx off) (read_result cx) st = (INL (IntV i), st)) /\
     dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32)))
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  `MEM off args /\ expr_type off = BaseT (UintT 256)` by
    (Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule_all create_call_operand_body_pre_mods >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `args = _` SUBST1_TAC >>
      simp[Once (cj 2 blueprint_offset_form)] >>
      irule blueprint_offset_literal_bit_mods >>
      conj_tac >- (Cases_on `hs` >> simp[]) >>
      qexistsl [`cenv`, `env`, `es`, `mods`] >> simp[] >>
      qpat_x_assum `contract_inv _ _ _ _ _` mp_tac >> simp[contract_inv_def]) >>
  rpt gen_tac >> strip_tac >>
  `expr_int_literal (origin_fold_value off) = SOME i` by simp[expr_int_literal_def] >>
  `!st. bind (eval_expr cx off) (read_result cx) st = (INL (IntV i),st)` by
    simp[blueprint_literal_offset_read] >>
  simp[] >>
  `bind (eval_expr cx off) (read_result cx) es = (INL (IntV i),es)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >> simp[] >>
  simp[value_runtime_typed_def] >> strip_tac >>
  drule_then SUBST_ALL_TAC evaluate_type_base_identity >>
  drule uint256_typed_dest >>
  simp[typed_val_to_w256_def, val_to_w256_def]
QED
