Theory bodyMemAggregateSide
Ancestors
  bodyMemAggregatePath exprSimAggregateSource exprSimHyps exprSimProps
  gasSummary venomMemDefs words

Theorem aggregate_child_read_typed_mem:
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es' (OK r) /\
  expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  !v. read_result cx tvv (es' with gas_obs := []) =
      (INL v,es' with gas_obs := []) ==>
      value_has_type tv v /\ val_wf tv v
Proof
  simp[gas_marked_exec_def] >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (irule aggregate_materialised_child_typed >>
      goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >> metis_tac[]) >>
  irule aggregate_materialised_child_wf >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >> metis_tac[]
QED

Theorem aggregate_child_memory_size_bound:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  type_memory_size tv < 2 ** 64
Proof
  strip_tac >> Cases_on `is_word_type (expr_type e)`
  >- (drule_all word_tv_memory_size >> simp[]) >>
  drule_all expr_body_pre_copy_ok >> simp[]
QED

Theorem aggregate_allocated_slice_capacity:
  alloca_inv r /\ FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
  off + k <= asz /\ b + asz < dimword (:256) ==>
  w2n (n2w (b+off) : bytes32) + k <= r.vs_alloca_next
Proof
  simp[alloca_inv_def, alloca_next_valid_def] >> rpt strip_tac >>
  `b + asz <= r.vs_alloca_next` by metis_tac[] >>
  `b + off < dimword (:256)` by decide_tac >>
  simp[w2n_n2w] >> decide_tac
QED
