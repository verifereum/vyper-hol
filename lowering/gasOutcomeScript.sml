(* Every path selects its gas marks before the finite observation horizon.
   Invalid source traces and exempt source executions need no final target post. *)
Theory gasOutcome
Ancestors
  gasSummary gasExemptCert gasStorage vyperState

Definition gas_outcome_def:
  gas_outcome memory tops p cx st0 source (es,s0) Q R <=>
    ?marks.
      gas_bad_storage_at cx st0 source es s0 marks \/
      gas_summary_at memory p marks source (es,s0)
        (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==>
          Q H res ee t)
        (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
          R H res ee r) \/
      ?err ee leaf finish.
        gas_exempt_cert memory tops p (ignore_bind source (return ()))
          (es,s0) marks (err,ee) (leaf,finish)
End

(* A trace-only source prefix spends no target instruction or gas mark. *)
Theorem gas_outcome_record_storage_event:
  gas_outcome memory tops (ctx,func) cx st0 source
    (es with storage_trace := es.storage_trace ++ [ev], s0) Q R /\
  ~s0.vs_halted ==>
  gas_outcome memory tops (ctx,func) cx st0
    (ignore_bind (record_storage_event ev) source) (es,s0) Q R
Proof
  `!gs. ignore_bind (record_storage_event ev) source (es with gas_obs := gs) =
     source ((es with storage_trace := es.storage_trace ++ [ev])
               with gas_obs := gs)` by
    simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
         vyperStateTheory.record_storage_event_def, vyperStateTheory.return_def] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def])
  >- (disj2_tac >> disj1_tac >>
      fs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target_end)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target_end`] >>
  `ignore_bind (ignore_bind (record_storage_event ev) source) (return ()) =
   bind (record_storage_event ev) (\u. ignore_bind source (return ()))` by
    simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  `marks = [] ++ marks` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_bind_unit >>
  qexistsl_tac [`es with storage_trace := es.storage_trace ++ [ev]`, `s0`, `()`] >>
  simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def, fragGasPathTheory.gas_path_rules,
       fragGasPathMemTheory.gas_path_mem_rules,
       vyperStateTheory.record_storage_event_def, vyperStateTheory.return_def] >>
  drule gas_exempt_cert_start_gas_obs >> simp[]
QED
