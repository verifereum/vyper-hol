(* Caller-side source layout facts for aggregate declaration relayout. *)
Theory annassignRelayoutSource
Ancestors
  annassignRelayoutPost memoryLocalRhsProps exprSimIfExpCompat
  exprSimHyps exprSimHypsDefs exprSimSource typedMemoryCopy supportedTypes supportedStmts
  valueTypingMemoryProps loweringPosts vyperTypeSystem vyperTypeInvariants
  exprLowering compileEnv vyperValue vyperAST vyperInterpreter
Libs monadsyntax

Theorem nonbytes_evaluated_val_footprint:
  !tenv ty tv v.
    ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
    val_footprint tv v = type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `ty` >> gvs[evaluate_type_def, is_bytestring_type_def, AllCaseEqs()] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[evaluate_type_def, is_bytestring_type_def, AllCaseEqs()] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[evaluate_type_def, is_bytestring_type_def]
QED

Theorem annassign_relayout_source_classify:
  !cenv cx env e es typ.
    expr_body_pre cenv cx env e es /\
    supported_copy_types typ (expr_type e) /\ ~is_word_type typ /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    expr_type e = typ /\ ~is_bytestring_type typ /\
    ~is_word_type (lowered_value_type cenv e) /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    post_value_type cenv e = lowered_value_type cenv e /\
    lowered_value_type cenv e <> expr_type e /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) typ /\
    ?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule ifexp_lowered_type_classify >>
  disch_then (qspec_then `cenv` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  drule ifexp_body_pre_intcall_physical >> strip_tac >>
  `~is_bytestring_type ty` by
    (gvs[expr_type_def] >> metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
  `typ = ty` by
    (qpat_x_assum `supported_copy_types _ _` mp_tac >>
     simp[supported_copy_types_def, expr_type_def] >>
     rpt strip_tac >> gvs[] >>
     BasicProvers.every_case_tac >>
     gvs[is_bytestring_type_def] >>
     metis_tac[typedCopyMetadataTheory.supported_word_type_is_word]) >>
  gvs[expr_type_def] >>
  drule ifexp_intcall_copy_source >> simp[] >> strip_tac >>
  `~is_word_type (lowered_value_type cenv (Call ty (IntCall fid) args drv))` by
    metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type (lowered_value_type cenv (Call ty (IntCall fid) args drv))` by
    metis_tac[type_widens_from_bytestring] >>
  simp[]
QED

Theorem annassign_relayout_read_layout:
  !cenv cx env e es tops typ stv tyv gs v es'.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    cenv.ce_func_return_type = build_func_return_type tops /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    type_widens_to env.type_defs (expr_type e) typ /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    ~is_bytestring_type (lowered_value_type cenv e) /\
    (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,es') ==>
    value_has_type stv v /\ value_has_type tyv v /\
    val_wf stv v /\ val_wf tyv v /\ val_footprint stv v = type_memory_size stv
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by fs[expr_body_pre_def] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    (drule_all memory_rhs_read_lowered_typed >> simp[]) >>
  `value_runtime_typed env typ v` by
    (drule_all memory_rhs_read_destination_typed >> simp[]) >>
  `value_has_type stv v /\ value_has_type tyv v` by
    metis_tac[memory_rhs_runtime_layout, optionTheory.SOME_11] >>
  simp[value_has_type_memory_wf] >>
  irule nonbytes_evaluated_val_footprint >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `get_tenv cx` >> simp[]
QED

Theorem arg_type_fits_memory_bytes_mono:
  (!sty dty. arg_type_fits sty dty ==>
    !cenv. type_memory_bytes cenv sty <= type_memory_bytes cenv dty) /\
  (!sts dts. arg_types_fit sts dts ==>
    !cenv. SUM (MAP (type_memory_bytes cenv) sts) <=
           SUM (MAP (type_memory_bytes cenv) dts))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[arg_type_fits_def, type_memory_bytes_def] >>
  rpt strip_tac >> gvs[ETA_THM] >>
  all_tac
  >>~- ([`(_ + 31) DIV 32 <= _`],
    irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  metis_tac[arithmeticTheory.LESS_MONO_MULT2, arithmeticTheory.LESS_EQ_LESS_EQ_MONO]
QED

Theorem widening_memory_layout_bound:
  !cenv cx env es sty typ stv tyv.
    expr_sim_inv cenv cx env es /\
    type_widens_to (get_tenv cx) sty typ /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    type_memory_bytes cenv typ < 2 ** 64 ==>
    type_memory_bytes cenv sty = type_memory_size stv /\
    type_memory_bytes cenv typ = type_memory_size tyv /\
    type_memory_bytes cenv sty <= type_memory_bytes cenv typ /\
    type_memory_bytes cenv sty < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes cenv sty <= type_memory_bytes cenv typ` by
    (fs[type_widens_to_def] >>
     metis_tac[cj 1 arg_type_fits_memory_bytes_mono]) >>
  `type_memory_bytes cenv sty = type_memory_size stv /\
   type_memory_bytes cenv typ = type_memory_size tyv` by
    metis_tac[expr_sim_inv_memory_size] >>
  gvs[wordsTheory.dimword_def] >> decide_tac
QED
