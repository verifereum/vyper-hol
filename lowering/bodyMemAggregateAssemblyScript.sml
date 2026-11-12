(* Source composition interfaces for memory-counted aggregate assembly.
   Immutable separation is already exported by bodyMemAggregateLoopBoundary. *)
Theory bodyMemAggregateAssembly
Ancestors
  bodyMemAggregateAdapters bodyMemAggregateLoopBoundary
  exprSimAggregateSource gasOutcome gasSummary gasContext fragGasMode
  vyperInterpreter vyperState vyperAST vyperValueOperation vyperValue

Theorem aggregate_outcome_map_mem:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q R /\
  (!H res ee t. Q H res ee t ==> Q' H (SUM_MAP f I res) ee t) /\
  (!H res ee r. R H res ee r ==> R' H (SUM_MAP f I res) ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind source (return o f)) (es,s)
    Q' R'
Proof
  strip_tac >>
  `ignore_bind (bind source (return o f)) (return ()) =
   ignore_bind source (return ())` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >>
     gen_tac >> Cases_on `source x` >> Cases_on `q` >> simp[]) >>
  `!st. SND (bind source (return o f) st) = SND (source st)` by
    (gen_tac >> simp[bind_def, return_def] >>
     Cases_on `source st` >> Cases_on `q` >> simp[]) >>
  gvs[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gasStorageTheory.gas_bad_storage_at_def])
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >> strip_tac >>
      qexistsl_tac [`SUM_MAP f I res`, `es_end`, `r`] >>
      simp[bind_def, return_def] >>
      Cases_on `res` >> gvs[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem aggregate_struct_action_mem:
  eval_expr cx (StructLit ann nsid fields) =
  bind (eval_exprs cx (MAP SND fields))
    (return o (\vs. Value (StructV (ZIP (MAP FST fields,vs)))))
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx (MAP SND fields) x` >>
  drule aggregate_eval_struct >>
  disch_then (qspecl_then [`nsid`,`ann`] mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem aggregate_tuple_action_mem:
  compatible_bound bnd (LENGTH args) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) args) =
  bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (TupleV vs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >>
  drule_all aggregate_eval_make_tuple >>
  disch_then (qspec_then `ann` mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem aggregate_array_action_mem:
  compatible_bound bnd (LENGTH args) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args) =
  bind (eval_exprs cx args)
    (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >>
  drule_all aggregate_eval_make_array >>
  disch_then (qspec_then `ann` mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem aggregate_outcome_source_run_mem:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q R ==>
  gas_outcome memory tops (ctx,func) cx st0 source (es,s)
    (\H res ee t. Q H res ee t /\ valid_horizon cx st0 H ee.storage_trace /\
       ?gs. source (es with gas_obs := gs) = (res,ee)) R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      first_x_assum (qspec_then `[]` assume_tac) >>
      gvs[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED
