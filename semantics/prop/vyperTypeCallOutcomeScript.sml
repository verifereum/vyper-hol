(* Guarded oracle type boundaries. No premise on the supplied oracle and no
 * protected-storage claim: account typing bounds balance/code, not storage.
 * Continuation/default errors are owned solely by the supplied IH.
 *)
Theory vyperTypeCallOutcome
Ancestors
  pair sum list option vyperState vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches
  vyperCallOutcomeFrame vyperRuntimeAccounts vyperTypeExtCallCore
  vyperTypeValues vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness vyperTypeEnv vyperTypeSystem
  vyperInterpreter vyperAST vyperValue vyperTyping
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);
val _ = hide "body";

(* One residual-record interface, rather than a per-field API matrix. *)
Theorem runtime_consistent_call_frame:
  runtime_consistent env cx st /\
  st' = st with <|accounts := st'.accounts; tStorage := st'.tStorage;
                  logs := st'.logs; outcomes := st'.outcomes;
                  requests := st'.requests; pending_deletions := st'.pending_deletions|> /\
  accounts_well_typed st'.accounts ==>
  runtime_consistent env cx st'
Proof
  rpt strip_tac >>
  `st'.scopes = st.scopes /\ st'.immutables = st.immutables` by
    (qpat_x_assum `st' = _` mp_tac >>
     simp[evaluation_state_component_equality]) >>
  gvs[runtime_consistent_def, state_well_typed_def, env_consistent_def,
      env_scopes_consistent_def, env_immutables_consistent_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem take_call_outcome_runtime_consistent:
  runtime_consistent env cx st /\
  take_call_outcome target calldata value_opt st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  rpt strip_tac >> drule take_call_outcome_frame >> strip_tac >>
  irule runtime_consistent_call_frame >> conj_tac
  >- gvs[evaluation_state_component_equality, runtime_consistent_def] >>
  qexists_tac `st` >> simp[] >>
  gvs[evaluation_state_component_equality]
QED

Theorem take_adopt_call_outcome_runtime_consistent:
  runtime_consistent env cx st /\
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  runtime_consistent env cx st2
Proof
  rpt strip_tac >> drule_all checked_call_outcome_success_frame >> strip_tac >>
  `accounts_runtime_well_typed st.accounts` by
    gvs[runtime_consistent_def, accounts_runtime_well_typed_accounts_well_typed] >>
  drule_all take_adopt_call_outcome_typed >> strip_tac >>
  irule runtime_consistent_call_frame >> conj_tac
  >- gvs[accounts_runtime_well_typed_accounts_well_typed] >>
  qexists_tac `st` >> simp[]
QED

(* Q is the actual expression postcondition; all new failures satisfy Q only
   through its RuntimeError rule. Successful take/adopt gives the IH its own
   typed accounts, not an assumption about all future payloads. *)
Theorem checked_call_outcome_type_sound:
  runtime_consistent env cx st /\
  (!s msg. runtime_consistent env cx s ==> Q (INR (Error (RuntimeError msg))) s) /\
  (!bs s res t. runtime_consistent env cx s /\ k bs s = (res,t) ==>
     runtime_consistent env cx t /\ Q res t) /\
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==>
  runtime_consistent env cx st' /\ Q res st'
Proof
  simp[checked_call_outcome_cases] >> rpt gen_tac >> strip_tac
  >- (drule_all take_call_outcome_runtime_consistent >> strip_tac >>
      drule take_call_outcome_error >> strip_tac >> gvs[] >> simp[])
  >- (drule_all take_call_outcome_runtime_consistent >> strip_tac >> gvs[] >> simp[]) >>
  drule_all take_adopt_call_outcome_runtime_consistent >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem Send_outcome_type_sound:
  runtime_consistent env cx st /\
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env (Call NoneT (Send has_gas) es extra) tv
  | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (checked_call_outcome_type_sound |>
    INST_TYPE [alpha |-> ``:toplevel_value``] |> Q.INST
    [`Q` |-> `\res t. no_type_error_result res /\
      case res of INL tv => expr_result_typed env (Call NoneT (Send has_gas) es extra) tv | INR _ => T`,
     `k` |-> `\bs. vyperState$return (Value NoneV)`] |> SRULE
    [return_def, no_type_error_result_def, expr_result_typed_def,
     expr_runtime_typed_def, expr_type_def, toplevel_value_typed_def,
     evaluate_type_def, value_has_type_def, is_HashMapRef_def]) >>
  disch_then (mp_tac o SPEC_ALL) >>
  simp[runtime_consistent_def, no_type_error_result_def,
       expr_result_typed_def, expr_runtime_typed_def, expr_type_def]
QED
