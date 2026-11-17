(* Marked source sequencing preserves conditional outcome-consumption credit.
   The second segment uses the real intermediate target GAS stream. *)
Theory loweringBudgetMarkedResidual
Ancestors
  gasSummaryCompose vyperEvalOutcomeSuffix arithmetic list

Theorem lower_budget_marked_bind_residual:
 !memory ctx func source next es s0 left v mid t right res fin r os ms rest a b.
 gas_marked_exec memory (ctx,func) source (es,s0) left (INL v) mid (OK t) /\
 gas_marked_exec memory (ctx,func) (next v)
   (mid with gas_obs := [],t) right res fin r /\
 es.outcomes = SOME os /\ mid.outcomes = SOME ms /\
 fin.outcomes = SOME rest /\
 outcome_suffix mid.outcomes fin.outcomes /\
 (ms <> [] ==> a + LENGTH ms <= LENGTH os) /\
 (rest <> [] ==> b + LENGTH rest <= LENGTH ms) ==>
 gas_marked_exec memory (ctx,func) (bind source next)
   (es,s0) (left ++ right) res fin r /\
 (rest <> [] ==> (a + b) + LENGTH rest <= LENGTH os)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule gas_marked_exec_bind_normal >> metis_tac[]) >>
  strip_tac >>
  `ms <> []` by (gvs[outcome_suffix_def]) >>
  gvs[]
QED
