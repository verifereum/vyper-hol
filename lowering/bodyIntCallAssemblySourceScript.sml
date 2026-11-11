Theory bodyIntCallAssemblySource
Ancestors
  bodyIntCallAssembly bodyIntCallCompletedFacts bodyIntCallCompletedSource
  bodyIntCallExemptReturn gasOutcome gasSummary gasContext fragGasFocus
  exprSimDefs vyperState vyperInterpreter
Libs
  monadsyntax

Theorem invoke_cleanup_outcome:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_admissible
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast tv rv) "IntCall cast ret";
        return (Value crv) od) expr_vv_res_ok es /\
  gas_outcome F tops (ctx,callee) f (es,entered) (\res ee r. F) R /\
  (!res ee r. R res ee r ==> expr_exit res r \/
    ?v ir cs. res = INL v /\ r = IntRet ir cs /\ P v ee ir cs) /\
  (!marks v ee ir cs.
    gas_marked_exec F (ctx,callee) f (es,entered) marks (INL v) ee (IntRet ir cs) /\
    P v (ee with gas_obs := []) ir cs /\ value_has_type tv v ==>
    ?k out. gas_path ctx func t (LENGTH marks + k) (OK out) /\
      Q (INL (Value v)) ((ee with scopes := prev) with gas_obs := []) out) ==>
  gas_outcome F tops (ctx,func)
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast tv rv) "IntCall cast ret";
        return (Value crv) od) (es,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> reverse strip_tac
  >- (qexists_tac `marks` >> disj2_tac >>
      irule_at Any gas_exempt_cert_value_cleanup >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [gas_summary_at_def]) >>
  first_x_assum drule >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule invoke_cleanup_exit_summary >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qpat_x_assum `r = IntRet ir cs` SUBST_ALL_TAC >>
  `value_has_type tv v` by
    (irule marked_cleanup_return_typed >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `marks ++ REPLICATE k F` >> disj1_tac >>
  drule_all invoke_cleanup_return_summary >> simp[]
QED
