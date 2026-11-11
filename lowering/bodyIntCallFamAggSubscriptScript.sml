(* Seam 2 joint induction, a family leaf of the agg step: subscripts (every place_type case).
   The residual array-place-base case is the held leaf
   bodyIntCallFamAggSubscriptHeldTheory.intcall_subscript_array_place_base_held;
   use it for that case. *)
Theory bodyIntCallFamAggSubscript
Ancestors
  bodyIntCallJointContract bodyIntCallJointWidened
  bodyIntCallFamAggSubscriptHeld bodyIntCallFamAggSubscriptTuple
  bodyIntCallFamAggSubscriptCompile bodyIntCallFamAggSubscriptRunCuts
  bodyIntCallFamAggSubscriptCuts bodyIntCallFamAggSubscriptResources
  bodyIntCallFamAggSubscriptScratch bodyIntCallFamAggSubscriptTailRun
  bodyIntCallFamAggSubscriptHashTail bodyIntCallFamAggSubscriptAllocRun
  bodyIntCallFamAggSubscriptWordRun bodyIntCallFamAggSubscriptArrayWindow
  bodyIntCallFamAggSubscriptArrayRun bodyIntCallFamAggSubscriptArrayPost
  bodyIntCallFamAggSubscriptArraySuffix bodyIntCallFamAggSubscriptArrayIndex
  bodyIntCallFamAggSubscriptMap bodyIntCallFamAggSubscriptArrayPrepare
  bodyIntCallFamAggSubscriptArrayCompose bodyIntCallFamAggSubscriptArraySequence
  bodyIntCallFamAggSubscriptArraySetup bodyIntCallFamAggSubscriptGas
  bodyIntCallFamAggSubscriptArrayProducer bodyIntCallFamAggSubscriptArrayDispatch
  bodyIntCallFamAggSubscriptBaseOutcome bodyIntCallFamAggSubscriptPosts
  bodyIntCallFamAggSubscriptMapValue bodyIntCallFamAggSubscriptTupleSource
  bodyIntCallFamAggSubscriptTupleSuffix bodyIntCallFamAggSubscriptTupleProducer

Theorem intcall_subscript_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base idx. e = Subscript a base idx) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> reverse conj_tac
  >- (irule intcall_subscript_map_step >> simp[] >> metis_tac[]) >>
  gvs[] >> rename1 `Subscript ann obj idx` >>
  rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  `post_value_type ce obj = expr_type obj` by
    (drule bodySimExprCasesTheory.expr_body_pre_subscript_base_type >> simp[]) >>
  `place_map_tables_agree_on_defined ce env /\
   (!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==> ce.ce_hashmap_info nsid = NONE)` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `well_typed_expr env (Subscript ann obj idx)` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[Once vyperTypeSystemTheory.well_typed_expr_def] >>
  strip_tac
  >- (suspend "value") >>
  suspend "place"
QED

Resume intcall_subscript_step[value]:
  `place_type ce obj = ValPT (expr_type obj)` by
    (irule placeTypingPropsTheory.place_type_well_typed_on_defined >> qexists_tac `env` >> simp[]) >>
  Cases_on `expr_type obj` >>
  fs[vyperTypeSystemTheory.subscript_type_ok_def]
  >- (suspend "tuple") >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_subscript_array_outcome >>
  simp[vyperASTTheory.expr_size_def] >>
  disch_then irule >> simp[]
QED

Resume intcall_subscript_step[place]:
  drule_all placeTypingPropsTheory.place_type_checked_place_on_defined >>
  strip_tac >>
  drule placeTypingPropsTheory.type_place_expr_vtype_annotation >> strip_tac >>
  Cases_on `vt` >>
  gvs[vyperTypeSystemTheory.subscript_vtype_def, exprLoweringTheory.value_type_place_def,
      vyperTypeSystemTheory.vtype_annotation_ok_def]
  >- (Cases_on `expr_type obj` >>
      gvs[vyperTypeSystemTheory.subscript_vtype_def] >>
      drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_subscript_array_outcome >>
      simp[vyperASTTheory.expr_size_def] >> disch_then irule >> simp[]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_subscript_mapping_outcome >>
  simp[vyperASTTheory.expr_size_def] >> disch_then irule >> simp[]
QED

Resume intcall_subscript_step[tuple]:
  `intcall_expr_producer fp obj` by
    (first_x_assum (qspec_then `obj` mp_tac) >> simp[]) >>
  `supported_place_info fp.jc_tops obj = place_type ce obj` by
    (pure_rewrite_tac[supportedExprFormsTheory.supported_place_info_def] >>
     irule exprLoweringTheory.place_type_env_cong >> fs[bodySimTheory.body_inv_def]) >>
  `supported_place_type fp.jc_tops (expr_type obj)` by
    fs[supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def,
       supportedExprFormsTheory.supported_subscript_place_def] >>
  `supported_expr fp.jc_tops obj` by
    (irule bodyIntCallFamAggSubscriptTypedSupportTheory.supported_subscript_value_base >> metis_tac[]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) intcall_subscript_tuple_producer >>
  simp[] >> disch_then irule >> simp[]
QED

Finalise intcall_subscript_step
