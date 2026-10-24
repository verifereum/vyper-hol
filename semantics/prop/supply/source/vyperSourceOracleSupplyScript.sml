(* TOP-LEVEL: source_supply_action_take and source_supply_action_adopt.
 * Helpers: residual payload safety and account replacement.
 *)
Theory vyperSourceOracleSupply
Ancestors
  list pair vyperSourceSupplyDefs vyperAccountSupply vyperSupplyBoundary
  vyperCallOutcome extCallOracle vyperState
Libs
  monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);

Definition supply_adoption_safe_def:
  supply_adoption_safe request outcome <=>
    (outcome.co_success /\ ~request.cr_static ==>
      accounts_supply_bounded outcome.co_accounts)
End

Theorem source_supply_action_update_accounts:
  (!accounts. accounts_supply_bounded accounts ==>
    accounts_supply_bounded (update accounts)) ==>
  source_supply_action (vyperState$update_accounts update)
Proof
  rw[source_supply_action_def, source_supply_def, update_accounts_def, return_def] >>
  first_x_assum irule >> simp[]
QED

Theorem source_supply_action_accounts_const:
  accounts_supply_bounded accounts ==>
  source_supply_action (update_accounts (K accounts))
Proof
  strip_tac >> irule source_supply_action_update_accounts >> simp[]
QED

Theorem source_supply_action_take:
  source_supply_action (take_call_outcome target calldata value_opt)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  Cases_on `take_call_outcome target calldata value_opt before` >>
  rename1 `take_call_outcome target calldata value_opt before = (result,post)` >>
  Cases_on `before.outcomes`
  >- gvs[take_call_outcome_NONE] >>
  drule take_call_outcome_frame >> strip_tac >>
  drule_all take_call_outcome_suffix >> strip_tac >>
  gvs[source_supply_def, supply_safe_outcomes_def, EVERY_APPEND,
      evaluation_state_component_equality]
QED

Theorem source_supply_take_safe_pair:
  source_supply before /\
  take_call_outcome target calldata value_opt before = (INL (request,outcome),post) ==>
  supply_adoption_safe request outcome
Proof
  strip_tac >> drule take_call_outcome_success >> strip_tac >>
  gvs[source_supply_def] >>
  `accounts_supply_bounded
     (call_outcome_request target calldata value_opt before).cr_accounts` by
    simp[call_outcome_request_def] >>
  drule_all supply_safe_take_outcome >> strip_tac >>
  simp[supply_adoption_safe_def]
QED

Theorem source_supply_take_safe:
  source_supply before /\
  take_call_outcome target calldata value_opt before = (INL payload,post) ==>
  supply_adoption_safe (FST payload) (SND payload)
Proof
  Cases_on `payload` >> simp[] >> strip_tac >>
  drule_all source_supply_take_safe_pair >> simp[]
QED

Theorem source_supply_action_adopt:
  supply_adoption_safe request outcome ==>
  source_supply_action (adopt_call_outcome request outcome)
Proof
  strip_tac >> simp[source_supply_action_def, adopt_call_outcome_equation] >>
  gen_tac >> strip_tac >>
  Cases_on `outcome.co_success /\ ~request.cr_static` >>
  gvs[source_supply_def, supply_adoption_safe_def]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourceOracleSupply");
