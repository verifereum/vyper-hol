Theory bodyPtrBytestringBuiltinsRuntime
Ancestors
  bodyPtrBytestringBuiltinsEval fragGasSeqPtr exprSimSource
  compileEnv finite_map list fragGasPathPtr

Theorem gas_outcome_ptr_nonhalted_post:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\ ~t.vs_halted) R
Proof
  rw[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  metis_tac[gas_path_ptr_ok_not_halted]
QED

(* The OK-path invariant supplies nonhalting, but no freshness assumption
   is present in the expression simulation entry contract. *)
Theorem populated_frontier_not_fresh:
  ~fresh_vars_wrt sa
    (s with vs_vars := s.vs_vars |+
      (STRING #"%" (toString sa.cs_next_var), 0w))
Proof
  simp[fresh_vars_wrt_def] >> qexists_tac `sa.cs_next_var` >> simp[]
QED

Theorem populated_frontier_reflexive_path:
  ~s.vs_halted ==>
  gas_path_ptr D lo ctx fn PG G tn
    (s with vs_vars := s.vs_vars |+ (STRING #"%" (toString sa.cs_next_var), 0w))
    0 G tn
    (OK (s with vs_vars := s.vs_vars |+ (STRING #"%" (toString sa.cs_next_var), 0w)))
Proof
  strip_tac >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
