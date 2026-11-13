(* Frozen tuple-assignment premises determine the physical call layout. *)
Theory tupleWidenedEntryPtr
Ancestors
  tupleWidenedSourceReady externalNormalizePremises assignTuplePtrBodyTargets
  tupleTargetStoreProps exprSimHyps exprSimHypsDefs vyperTypeValues
  vyperTypeInvariants vyperTypeSystem vyperValue valueEncoding
  supportedStmts supportedExprs supportedTypes memoryLocalRhsProps bodySim
  exprLowering loweringPosts list

Theorem tuple_widened_entry_ready_ptr:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  lowered_value_type cenv e <> expr_type e ==>
  expr_body_pre cenv cx env e es /\
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target tops bindings bt) gs /\
  ?atys stys stvs.
    expr_type e = TupleT atys /\ ~is_memory_view e /\
    lowered_value_type cenv e = TupleT stys /\
    post_value_type cenv e = TupleT stys /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    0 < type_memory_size_list stvs /\ LENGTH gs = LENGTH stys /\
    LIST_REL (\sty stv. evaluate_type (get_tenv cx) sty = SOME stv) stys stvs /\
    LIST_REL (\sty stv. type_memory_bytes cenv sty = type_memory_size stv) stys stvs
Proof
  strip_tac >>
  drule_all tuple_rhs_body_pre_ptr >> disch_tac >>
  drule tuple_targets_typing >>
  disch_then (qx_choose_then `atys` strip_assume_tac) >>
  drule_all tuple_widened_source_ready >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`fid`, `args`, `drv`, `stys`, `stvs`] strip_assume_tac)) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (TupleT stys) (expr_type e) /\
   TupleT stys <> expr_type e` by metis_tac[post_value_type_widens] >>
  `0 < type_memory_size_list stvs` by
    (drule_all normalize_return_source_positive >> simp[type_memory_size_def]) >>
  `LIST_REL (\sty stv. evaluate_type (get_tenv cx) sty = SOME stv) stys stvs` by
    (drule evaluate_type_TupleT_cases >> strip_tac >> gvs[]) >>
  `LIST_REL (\sty stv. type_memory_bytes cenv sty = type_memory_size stv) stys stvs` by
    (irule LIST_REL_mono >>
     qexists_tac `\sty stv. evaluate_type (get_tenv cx) sty = SOME stv` >>
     simp[] >> metis_tac[expr_sim_inv_memory_size]) >>
  `EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target tops bindings bt) gs` by
    (`!g. MEM g gs ==> (case g of
        BaseTarget bt => supported_target tops bindings bt | TupleTarget _ => F)` by
       fs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
     simp_tac std_ss [EVERY_MEM] >> qx_gen_tac `g` >> strip_tac >>
     qpat_x_assum `!g. MEM g gs ==> _` drule >> Cases_on `g` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`atys`, `stys`, `stvs`] >> simp[] >>
  metis_tac[LIST_REL_LENGTH]
QED

(* Supported internal return tuples contain words and bytelike values. *)
Theorem tuple_widened_physical_scalars_ptr:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT atys /\
  lowered_value_type cenv e = TupleT stys /\
  lowered_value_type cenv e <> expr_type e ==>
  EVERY supported_scalar_type stys
Proof
  strip_tac >> drule_all tuple_widened_source_ready >> strip_tac >> gvs[] >>
  `supported_program tops /\
   cenv.ce_func_return_type = build_func_return_type tops` by
    fs[body_inv_def] >>
  qpat_x_assum `supported_expr _ _` mp_tac >>
  simp[supported_expr_def,supported_pure_expr_def,supported_effect_expr_def] >>
  strip_tac >> Cases_on `drv` >>
  gvs[supported_effect_expr_def,optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `x` >>
  drule_all supported_internal_return_type >> strip_tac >>
  drule_all supported_internal_return_admissible >> strip_tac >>
  gvs[lowered_value_type_def,supported_return_type_def,supported_value_tuple_depth]
QED
