(* Counted continuation boundaries for EC arithmetic. *)
Theory bodyMemEcArithCompose
Ancestors
  stmtReasonVvMemory gasSummary fragGasPath fragGasMode exprSimDefs vyperState

(* Adapter for private exprSimECArith.ec_outcome_then, using the exported
   memory-polymorphic gas_outcome_bind_value rather than duplicating its
   normal/exception/exemption composition proof. *)
Theorem ec_mem_outcome_then:
  gas_outcome T tops (ctx,func)
    (m : evaluation_state -> value evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t) (\res ee r. expr_exit res r) /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==>
     R (INR exc) ee r) /\
  (!gs v ee t. m (es with gas_obs := gs) = (INL v, ee) /\ ee.gas_obs = [] /\
     P v ee t /\ ~t.vs_halted ==>
     gas_outcome T tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome T tops (ctx,func) (bind m k) (es,s0) Q R
Proof
  strip_tac >> irule gas_outcome_bind_value >>
  first_assum (irule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `~t.vs_halted` by
        metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
      strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
      strip_tac >> first_x_assum irule >> simp[] >>
      goal_assum (drule_at Any)) >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
  metis_tac[]
QED
