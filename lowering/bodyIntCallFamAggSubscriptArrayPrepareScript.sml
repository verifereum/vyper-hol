(* Source normalization for counted array children. *)
Theory bodyIntCallFamAggSubscriptArrayPrepare
Ancestors
  gasSummary exprSimSubscriptArraySource exprSimSource vyperState

Theorem intcall_array_children_source:
  gas_marked_exec memory (ctx,func) (eval_expr cx obj)
    (es,s0) marks (INL r) mid (OK u) /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx idx) (read_result cx))
    (mid with gas_obs := [],u) imarks (INL iv) raw out ==>
  eval_expr cx obj
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                         gas_explicit imarks u.vs_gas_readings) =
    (INL r,mid with gas_obs := gas_explicit imarks u.vs_gas_readings) /\
  ?ir. eval_expr cx idx
      (mid with gas_obs := gas_explicit imarks u.vs_gas_readings) =
      (INL ir,raw with gas_obs := []) /\
    read_result cx ir (raw with gas_obs := []) =
      (INL iv,raw with gas_obs := [])
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >>
      disch_then (qspec_then `gas_explicit imarks u.vs_gas_readings` mp_tac o CONJUNCT1) >>
      simp[]) >>
  `bind (eval_expr cx idx) (read_result cx)
     (mid with gas_obs := gas_explicit imarks u.vs_gas_readings) =
     (INL iv,raw with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  pop_assum mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Theorem intcall_array_index_source_typed:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  eval_expr cx obj es = (INL r,mid) /\
  eval_expr cx idx mid = (INL ir,raw) /\
  read_result cx ir raw = (INL iv,raw) /\
  (!s r t. eval_expr cx idx s = (INL r,t) ==>
     t.scopes = s.scopes /\ t.immutables = s.immutables) ==>
  expr_body_pre ce cx env idx mid /\
  raw.scopes = mid.scopes /\ raw.immutables = mid.immutables /\
  ?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\
       value_has_type tv iv
Proof
  strip_tac >>
  `expr_body_pre ce cx env idx mid` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >>
     simp[] >> qexists_tac `ann` >> simp[]) >>
  simp[] >>
  `raw.scopes = mid.scopes /\ raw.immutables = mid.immutables` by
    (first_x_assum drule >> simp[]) >>
  simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  metis_tac[]
QED
