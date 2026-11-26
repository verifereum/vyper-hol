(* The source's blueprint-offset test and the compiler use the same folded literal. *)
Theory blueprintLiteralOffsetProps
Ancestors
  abiValueEncoding alist bodySim compileEnv constSubst constSubstStmtsPreserve exprBodyPreProps
  exprLowering exprSimHypsDefs exprSimSend exprSimSource gasContext integer_word
  list option supportedExprTraverse valueEncoding vyperAST vyperCreate
  vyperInterpreter vyperOriginFold vyperPinFold vyperPinFoldProps
  vyperState vyperTypeSystem vyperValue vyperValueOperation words

Theorem blueprint_offset_form:
  ((case e of Literal _ (IntL i) => comp_return (Lit (i2w i)) | _ => f) =
     (case expr_int_literal e of SOME i => comp_return (Lit (i2w i)) | NONE => f)) /\
  (is_int_literal e = IS_SOME (expr_int_literal e))
Proof
  Cases_on `e` >> simp[expr_int_literal_def,vyperPinFoldTheory.is_int_literal_def] >>
  rename1 `Literal _ l` >> Cases_on `l` >>
  simp[expr_int_literal_def,vyperPinFoldTheory.is_int_literal_def]
QED

Theorem blueprint_offset_literal_bit:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env offset es /\
  LENGTH salts = (if salted then 1 else 0) ==>
  blueprint_literal_offset cx salted (target::amount::(salts ++ offset::ctor)) =
    IS_SOME (expr_int_literal (origin_fold_value offset))
Proof
  strip_tac >>
  qpat_assum `body_inv _ _ _ _` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `subst_consts_expr (case get_module_code cx NONE of
      SOME tops => module_consts_env tops [] | NONE => []) offset = offset` by
    (Cases_on `get_module_code cx NONE`
     >- simp[constSubstTheory.subst_consts_expr_empty] >>
     simp[] >> irule (cj 1 constSubstStmtsPreserveTheory.subst_consts_expr_unchanged) >>
     drule expr_body_pre_static_facts >> strip_tac >> CCONTR_TAC >> gvs[] >>
     qpat_assum `supported_expr_exists _ offset`
       (mp_then Any (qspec_then `const_name_root cx` mp_tac)
         (cj 1 supportedExprTraverseTheory.supported_expr_exists_mono)) >>
     impl_tac
     >- (rpt strip_tac >> gvs[exprSimHypsDefsTheory.const_name_root_def,
           exprSimHypsDefsTheory.cx_const_name_def,gasContextTheory.cx_tops_def,
           optionTheory.IS_SOME_EQ_NOT_NONE] >>
         metis_tac[alistTheory.ALOOKUP_NONE]) >>
     simp[]) >>
  qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]`
    (fn code => rewrite_tac [MATCH_MP blueprint_literal_offset_singleton code]) >>
  Cases_on `salted` >> gvs[LENGTH_EQ_NUM_compute, blueprint_offset_form]
QED

Theorem blueprint_literal_offset_read:
  expr_int_literal (origin_fold_value e) = SOME i ==>
  bind (eval_expr cx e) (read_result cx) st = (INL (IntV i),st)
Proof
  `!x. expr_int_literal x = SOME i ==> ?ty. x = Literal ty (IntL i)` by
    (Cases >> simp[expr_int_literal_def] >> rename1 `Literal _ l` >>
     Cases_on `l` >> simp[expr_int_literal_def]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  drule vyperPinFoldPropsTheory.origin_fold_value_literal_sound >>
  disch_then (qspecl_then [`st`,`cx`] assume_tac) >>
  simp[bind_def,vyperValueOperationTheory.evaluate_literal_def,read_result_def,return_def]
QED

Theorem blueprint_literal_offset_word:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  expr_int_literal (origin_fold_value e) = SOME i ==>
  dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32))
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `?tyv. evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\ value_has_type tyv (IntV i)` by
    (drule exprSimSourceTheory.operand_eval_evidence_semantics >>
     disch_then (qspecl_then [`IntV i`,`[]`,`es with gas_obs := []`] mp_tac) >>
     simp[] >> (impl_tac >- (qexistsl [`[]`,`es`] >> simp[blueprint_literal_offset_read])) >>
     simp[]) >>
  `tyv = BaseTV (UintT 256)` by metis_tac[abiValueEncodingTheory.evaluate_type_base_result] >>
  gvs[] >> drule exprSimSendTheory.uint256_typed_dest >>
  simp[valueEncodingTheory.typed_val_to_w256_def,valueEncodingTheory.val_to_w256_def]
QED
