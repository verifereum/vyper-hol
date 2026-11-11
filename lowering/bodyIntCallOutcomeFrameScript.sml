(* Attach independent terminal resources to the counted semantic witness.
   Exempt certificates do not assert a terminal resource execution. *)
Theory bodyIntCallOutcomeFrame
Ancestors
  gasOutcome gasSummary fragGasMode fragGasPath fragExec
  bodyIntCallReachableReturn

Theorem gas_outcome_exit_attach:
  gas_outcome F tops (ctx,func) source (es,s) Q R /\
  (!n r. gas_path ctx func s n r /\ exit_result r ==> H r) ==>
  gas_outcome F tops (ctx,func) source (es,s) Q
    (\res ee r. R res ee r /\ H r)
Proof
  pure_rewrite_tac [gas_outcome_def, gas_summary_at_def,
                    gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[]
QED

(* Conditional fitting boundary: the fragment certificate and its entry
   predicate must still be supplied by the compiler resource producer. *)
Theorem gas_outcome_exit_fragment_attach:
  gas_outcome F tops (ctx,func) source (es,s) Q R /\
  frag_exec ctx sa sb P (\u. F) H /\
  fn_has_code sa sb func /\ P s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F tops (ctx,func) source (es,s) Q
    (\res ee r. R res ee r /\ H r)
Proof
  strip_tac >> irule gas_outcome_exit_attach >> simp[] >>
  rpt strip_tac >> irule exit_fragment_path_post >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
