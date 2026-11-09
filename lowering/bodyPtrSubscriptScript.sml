(*
 * Subscripts: a storage place owes ptr_vv_ok's taint bound (storage_read_live, stor_taint_ok).
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * As S1's body_subscript_case: a base the lowering lays out at another
 * type than its own (a widening internal call) is the residual
 * bodyPtrSubscriptWidenedResidual.  The rest by place_type of the base, as
 * S1's compile_subscript_case: a mapping (bodyPtrSubscriptSeamMap, over the
 * base's judgment from the residual bodyPtrSubscriptMapResidual), a tuple
 * (bodyPtrSubscriptSeamTuple), an array whose index frames its base in
 * memory or in code (bodyPtrSubscriptSeamArrayMemory,
 * bodyPtrSubscriptSeamArrayCode), and every other array (the residual
 * bodyPtrSubscriptArrayPlaceResidual).  No other base type dispatches
 * (bodyPtrSubscriptCaseSplit).
 *
 * TOP-LEVEL:
 *   subscript_expr_ptr_ok
 *)
Theory bodyPtrSubscript
Ancestors
  bodyPtrSubscriptCaseSplit bodyPtrSubscriptTupleDispatch
  bodyPtrSubscriptSeamTuple bodyPtrSubscriptSeamArrayMemory
  bodyPtrSubscriptSeamArrayCode bodyPtrSubscriptSeamMap
  bodyPtrSubscriptArrayPlaceResidual bodyPtrSubscriptMapResidual
  bodyPtrSubscriptWidenedResidual
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem subscript_expr_ptr_ok:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 ==>
    body_expr_ptr_ok cx (Subscript v8 e1 e2)
Proof
  rpt gen_tac >> strip_tac >> ONCE_REWRITE_TAC[body_expr_ptr_ok_def] >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `post_value_type cenv e1 = expr_type e1`)
  >- (qspecl_then [`cx`,`v8`,`e1`,`e2`] mp_tac
        body_subscript_widened_call_base_ptr >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then [`d`,`PG`,`tops`,`ctx`,`func`,`cenv`,`env`,
                               `ty`,`es`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript v8 e1 e2) es`
    suffices_by (strip_tac >> asm_rewrite_tac[] >>
                 irule expr_sim_ptr_of_vv >> conj_tac
                 >- (qexists_tac `env` >> first_assum ACCEPT_TAC) >>
                 first_assum ACCEPT_TAC) >>
  Cases_on `place_type cenv e1`
  >- (rename1 `MapPT kt vt` >>
      qspecl_then [`cx`,`v8`,`e1`,`e2`,`d`,`PG`,`tops`,`ctx`,`func`,`cenv`,
                   `env`,`ty`,`es`,`kt`,`vt`] mp_tac
        body_subscript_map_base_ptr >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qspecl_then [`cx`,`v8`,`e1`,`e2`,`d`,`PG`,`tops`,`ctx`,`func`,`cenv`,
                   `env`,`ty`,`es`,`kt`,`vt`] mp_tac subscript_map_ptr >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  rename1 `ValPT bt` >>
  drule_all subscript_value_base_type >> strip_tac >>
  qpat_x_assum `bt = _` SUBST_ALL_TAC >>
  qpat_x_assum `place_type cenv e1 = _` mp_tac >> asm_rewrite_tac[] >>
  strip_tac
  >- suspend "array" >>
  `expr_body_pre cenv cx env e1 es` by
    (drule_all tuple_subscript_pre >> strip_tac) >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty e1 es` by
    (qpat_x_assum `body_expr_ptr_ok cx e1`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  qspecl_then [`d`,`ctx`,`PG`,`func`,`cenv`,`cx`,`env`,`ty`,`v8`,`e1`,`e2`,
               `es`,`tys`] mp_tac subscript_tuple_vv_sim_ptr >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Resume subscript_expr_ptr_ok[array]:
  Cases_on `(!t r t'. eval_expr cx e2 t = (INL r, t') ==>
                      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
            (!s tr slot vt t.
               eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
            ((~cenv.ce_is_ctor /\
              !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
             ((?n. bd = Fixed n) /\
              (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
              !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))`
  >- (qpat_x_assum `(!t r t'. _) /\ _` strip_assume_tac
      >- (qspecl_then [`cx`,`v8`,`e1`,`e2`,`d`,`PG`,`tops`,`ctx`,`func`,
                       `cenv`,`env`,`ty`,`es`,`et`,`bd`] mp_tac
            subscript_array_framed_code_ptr >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC) >>
      qpat_x_assum `bd = _` SUBST_ALL_TAC >>
      qspecl_then [`cx`,`v8`,`e1`,`e2`,`d`,`PG`,`tops`,`ctx`,`func`,
                   `cenv`,`env`,`ty`,`es`,`et`,`n`] mp_tac
        subscript_array_framed_memory_ptr >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  qspecl_then [`cx`,`v8`,`e1`,`e2`,`d`,`PG`,`tops`,`ctx`,`func`,`cenv`,
               `env`,`ty`,`es`,`et`,`bd`] mp_tac
    body_subscript_array_place_base_ptr >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise subscript_expr_ptr_ok
