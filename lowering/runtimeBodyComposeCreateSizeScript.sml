(* Retain the CREATE-size clause when passing a body exit to composition. *)
Theory runtimeBodyComposeCreateSize
Ancestors
  gasOutcomeFull createSizeExit

Theorem gas_outcome_full_record_create_size:
  gas_outcome_full (DF,lo,E,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q
    (\H res ee gt r. create_size_exit_ok ctx res r /\ R H res ee gt r) <=>
  gas_outcome_full (DF,lo,E,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q R
Proof
  `!p q. (p /\ p /\ q) <=> (p /\ q)` by metis_tac[] >>
  simp[gas_outcome_full_def]
QED
