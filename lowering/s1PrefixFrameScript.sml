(* Request-free fragments use the empty GAS focus. *)
Theory s1PrefixFrame
Ancestors
  s1PrefixDefs gasOutcomeFull gasSummary vyperStorageFootprint
  vyperStorageTrace vyperState venomState list

Theorem gas_prefix_full_no_outcome:
  ~s.vs_halted /\ storage_trace_frame source /\
  (!gobs res ee. source (es with gas_obs := gobs) = (res, ee) ==>
     EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
       (DROP (LENGTH es.storage_trace) ee.storage_trace)) ==>
  gas_prefix_full P cx st0 source (es, s, G, tn)
Proof
  PairCases_on `P` >>
  rename1 `gas_prefix_full (_, _, _, _, func, PG) _ _ _ _` >> strip_tac >>
  simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`,
                    `func`, `PG`, `G`, `tn`, `s`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[DROP_APPEND1, EVERY_APPEND]
QED
