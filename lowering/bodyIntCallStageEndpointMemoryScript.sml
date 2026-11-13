(* A producer followed immediately by allocation, forcing, and typed store. *)
Theory bodyIntCallStageEndpointMemory
Ancestors
  bodyIntCallStageEndpointLanding bodyIntCallStageEndpointStore
  bodyIntCallCompilerTags
  bodyIntCallFamStmtReturnTypes bodyIntCallFamStmtLogArgsFrame
  exprSimAggregateChildren memoryLocalRhsProps typedMemoryCopy
  bodyIntCallJointForce exprSimSource exprSimMemDefs stmtSimForLoop
  exprBopSimProps exprSimHyps valueEncodingTyping exprLoweringProps

Theorem stage_incompatible_geometry[local]:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  (!src:256 word. ~is_word_type sty /\ val_footprint stv v <> 0 /\
    eval_operand op u = SOME src ==>
    regions_disjoint (w2n src) (val_footprint stv v) (w2n dw) cap) /\
  type_memory_size dtv <= cap /\
  (sty <> NoneT /\ ~is_word_type sty /\ ~is_bytestring_type sty ==>
    ?src:256 word a k. eval_operand op u = SOME src /\ a <= w2n src /\
      w2n src + type_memory_size stv <= a+k /\ a+k < dimword (:256)) ==>
  ~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
  !src:256 word. eval_operand op u = SOME src ==>
    regions_disjoint (w2n src) (type_memory_size stv)
      (w2n dw) (type_memory_size dtv) /\
    w2n src + type_memory_size stv < dimword (:256)
Proof
  rpt strip_tac >>
  `~is_word_type sty` by metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type sty` by
    (fs[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target]) >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  Cases_on `type_memory_size stv = 0`
  >- (drule_all widening_zero_memory_size >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def, wordsTheory.w2n_lt]) >>
  `sty <> NoneT` by
    (Cases_on `sty` >> gvs[vyperValueTheory.evaluate_type_def,
      valueEncodingTheory.type_memory_size_def]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem stage_call_tag[local]:
  vv_type (FST (compile_call cfn ce ann ty target args drv st)) =
    (case target of IntCall fid => ce.ce_func_return_type (nsid_to_string fid)
      | _ => ann)
Proof
  Cases_on `target`
  >~ [`ExtCall b c p opts`] >-
    (PairCases_on `p` >> Cases_on `args` >>
     simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
          contextTheory.vv_type_def] >>
     rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def])) >>
  (namedCases_on `args` ["", "a rest"]
  >- (simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
           contextTheory.vv_type_def] >>
      rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def])) >>
  namedCases_on `rest` ["", "b rest2"]
  >- (simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
           contextTheory.vv_type_def] >>
      rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def])) >>
  Cases_on `rest2` >>
  simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
       contextTheory.vv_type_def] >>
  rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def]))
QED

Theorem stage_expr_root_tag[local]:
  vv_type (FST (compile_expr ce (expr_type e) e st)) =
    (case e of Call ann (IntCall fid) args drv =>
       ce.ce_func_return_type (nsid_to_string fid) | _ => expr_type e)
Proof
  Cases_on `expr_effect_root e`
  >- (Cases_on `e` >> gvs[supportedExprTraverseTheory.expr_effect_root_def] >>
      once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
      simp[exprLoweringTheory.compile_expr_body_def, stage_call_tag,
           pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def] >>
      Cases_on `t` >> simp[stage_call_tag]) >>
  `vv_type (FST (compile_expr ce (expr_type e) e st)) = expr_type e` by
    (once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
     irule intcall_expr_body_tag >> simp[] >> conj_tac >> rpt gen_tac >>
     IF_CASES_TAC >> simp[exprCallBoundsTheory.invalid_expr_call_def, contextTheory.vv_type_def] >>
     once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
     simp[intcall_builtin_dispatch_body_tag, intcall_type_dispatch_body_tag,
          pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def]) >>
  simp[] >> Cases_on `e` >> gvs[supportedExprTraverseTheory.expr_effect_root_def]
QED

Theorem stage_compiler_store_post_type[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  type_widens_to tenv (expr_type e) dty ==>
  compile_store_memory ce src dst dty (vv_type vv) =
  compile_store_memory ce src dst dty (post_value_type ce e)
Proof
  strip_tac >>
  Cases_on `is_word_type dty` >- simp[contextTheory.compile_store_memory_def] >>
  Cases_on `is_bytestring_type dty` >- simp[contextTheory.compile_store_memory_def] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[type_widens_from_word, typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `vv_type vv = (case e of Call ann (IntCall fid) args drv =>
     ce.ce_func_return_type (nsid_to_string fid) | _ => expr_type e)` by
    metis_tac[stage_expr_root_tag, pairTheory.FST] >>
  Cases_on `e` >> gvs[loweringPostsTheory.post_value_type_def,
                         vyperASTTheory.expr_type_def] >>
  rename1 `Call ann target args drv` >> Cases_on `target` >>
  gvs[loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def,
      exprLoweringTheory.lowered_value_type_def]
QED
