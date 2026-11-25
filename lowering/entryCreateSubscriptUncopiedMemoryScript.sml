Theory entryCreateSubscriptUncopiedMemory
Ancestors
  entryCreateCompletedCut gasSummary

(* The selector preserves the source state except for the observation tail.
   Keep its actual return or abort and the same ghosts at every horizon. *)
Theorem nocopy_selector_scoped_landing:
  create_operand_full_scope sn sb E C f s [] r /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (r,G1,tn1) /\
    ((?t. r = OK t /\ Q H res (es with gas_obs := []) G1 tn1 t) \/
     (exit_result r /\ R H res (es with gas_obs := []) (G1,tn1) r))) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sn sb
    source (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`es`,`r`,`G1`,`tn1`] >>
  simp[gas_explicit_def]
QED
