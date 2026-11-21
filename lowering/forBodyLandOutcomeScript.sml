(* Lift a raw loop-body landing through the zero-mark suffix and source cleanup. *)
Theory forBodyLandOutcome
Ancestors
  bodyFullForHandlers gasOutcomeFull gasOutcomeFullCompose bodyPtrDefs exprSimDefs
  fragGasOriginPtr fragExec venomState vyperInterpreter vyperState haltExitProj
Libs monadsyntax

Theorem for_body_cleanup_from_raw_landing:
  eb.scopes <> [] /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmts cx stmts) (eb,s,G,tn) Qraw
    (\H raw ef gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ef with gas_obs := tail) raw gt r) /\
      halt_exit H cx ef raw r /\
      (ctx_has_dalloca ctx ==>
       !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u)) /\
  (!H raw ef G1 tn1 t.
    valid_horizon cx st0 H ef.storage_trace /\ Qraw H raw ef G1 tn1 t ==>
    ?sc rest b. ef.scopes = sc::rest /\
      (case raw of INL () => INL F
         | INR ex => FST (handle_loop_exception ex ef)) = INL b /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK (if raw = INL () then jump_to incr t else t),G1,tn1) /\
      (ef with scopes := rest).gas_obs = [] /\
      ~(if raw = INL () then jump_to incr t else t).vs_halted /\
      (b ==> Done H (ef with scopes := rest) G1 tn1
               (if raw = INL () then jump_to incr t else t)) /\
      (~b ==> Again H (ef with scopes := rest) G1 tn1
                (if raw = INL () then jump_to incr t else t))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (finally (try (do eval_stmts cx stmts; return F od)
                  handle_loop_exception) pop_scope) (eb,s,G,tn)
    (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
      ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\
                         (~b ==> Again H ee G1 tn1 t))
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==>
       !u. r = Halt u \/ (?ir. r = IntRet ir u) ==> allocas_below_fmp u))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full fp _ _ _ _ _ Qraw Rraw` >>
  qabbrev_tac `Qland = (\H (raw : unit + exception) ef GG tt u.
    ?sc rest b. ef.scopes = sc::rest /\
      (case raw of INL () => INL F
         | INR ex => FST (handle_loop_exception ex ef)) = INL b /\
      (ef with scopes := rest).gas_obs = [] /\ ~u.vs_halted /\
      (b ==> Done H (ef with scopes := rest) GG tt u) /\
      (~b ==> Again H (ef with scopes := rest) GG tt u))` >>
  `gas_outcome_full fp tops cx st0 (eval_stmts cx stmts)
      (eb,s,G,tn) Qland Rraw` by
    (qunabbrev_tac `fp` >> irule gas_outcome_full_zero_suffix >>
     qexists_tac `Qraw` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     map_every qx_gen_tac [`raw`, `ef`, `G1`, `tn1`, `t`] >> strip_tac >>
     qexistsl_tac [`if raw = INL () then jump_to incr t else t`, `G1`, `tn1`] >>
     qx_gen_tac `H` >> strip_tac >>
     first_x_assum (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!H raw ef G1 tn1 t. _` drule_all >>
     simp[NoAsms] >> disch_then (qx_choose_then `sc` (qx_choose_then `rest`
       (qx_choose_then `b` strip_assume_tac))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, Abbr `Qland`] >> qexistsl_tac [`sc`, `rest`, `b`] >>
     asm_rewrite_tac[]) >>
  qunabbrev_tac `fp` >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Qland Rraw`
    (mp_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) mp_tac for_body_cleanup_full) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) mp_tac
    gas_outcome_full_post_mono) >>
  disch_then irule >>
  conj_tac >- suspend "normal" >> suspend "exit"
QED

Resume for_body_cleanup_from_raw_landing[normal]:
  map_every qx_gen_tac [`H`, `out`, `ee`, `G1`, `tn1`, `t`] >> BETA_TAC >>
  disch_then (qx_choose_then `raw` (qx_choose_then `sc` strip_assume_tac)) >>
  qpat_x_assum `Qland H raw _ G1 tn1 t` mp_tac >>
  simp[NoAsms, Abbr `Qland`, evaluation_state_accfupds] >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  `out = INL b` by
    (qpat_x_assum `out = _` SUBST1_TAC >>
     qpat_x_assum `_ = INL b` mp_tac >>
     Cases_on `raw` >> simp[NoAsms] >>
     rename1 `handle_loop_exception ex _` >> Cases_on `ex` >>
     simp[NoAsms, handle_loop_exception_def, return_def, raise_def]) >>
  metis_tac[]
QED

Resume for_body_cleanup_from_raw_landing[exit]:
  map_every qx_gen_tac [`H`, `out`, `ee`, `gt`, `r`] >> BETA_TAC >>
  disch_then (qx_choose_then `raw` (qx_choose_then `sc` strip_assume_tac)) >>
  `?ex. raw = INR ex /\ out = INR ex` by
    (qpat_assum `out = _` SUBST1_TAC >>
     qpat_assum `Rraw H raw _ gt r` mp_tac >>
     simp[NoAsms, Abbr `Rraw`] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >>
     Cases_on `raw` >> simp[NoAsms, stmt_exit_ptr_def, oneline expr_exit_def] >>
     rename1 `_ = INR ex` >> Cases_on `ex` >> simp[NoAsms] >>
     Cases_on `r` >> simp[NoAsms]) >>
  qexists_tac `ex` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `raw = INR ex` SUBST_ALL_TAC >>
  qpat_x_assum `Rraw H (INR ex) _ gt r` mp_tac >>
  qunabbrev_tac `Rraw` >> BETA_TAC >>
  disch_then (mp_tac o MATCH_MP for_full_exit_scopes_gas_obs) >>
  disch_then (qspecl_then [`ee.scopes`, `ee.gas_obs`] mp_tac) >>
  `((ee with scopes := sc::ee.scopes) with
     <|scopes := ee.scopes; gas_obs := ee.gas_obs|>) = ee` by
    simp[NoAsms, evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> simp[NoAsms, halt_exit_INR_type] >>
  disch_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2)
QED

Finalise for_body_cleanup_from_raw_landing
