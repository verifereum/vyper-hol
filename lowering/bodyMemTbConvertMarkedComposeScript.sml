(* Mark-preserving bind composition for memory-safe convert branches. *)
Theory bodyMemTbConvertMarkedCompose
Ancestors gasSummary gasSummaryCompose fragGasMode vyperState vyperInterpreter list
  bodyMemTbConvertDynamicScalar bodyMemTbConvertSourceUnwrap

Theorem convert_mem_summary_bind:
  gas_summary_at T (ctx,func) marks source (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!v ee t. P v ee t ==>
     gas_summary_at T (ctx,func) [] (next v) (ee,t) Q R) ==>
  gas_summary_at T (ctx,func) marks (bind source next) (es,s0) Q R
Proof
  rewrite_tac[gas_summary_at_def] >> strip_tac
  >- suspend "normal" >>
  gvs[] >> qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED

Resume convert_mem_summary_bind[normal]:
  gvs[] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >> gvs[]
QED

Finalise convert_mem_summary_bind
