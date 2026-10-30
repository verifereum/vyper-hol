(* TOP-LEVEL: source_supply, source_supply_action and monadic composition.
 *)
Theory vyperSourceSupplyDefs
Ancestors
  list pair option vyperAccountSupply vyperSupplyBoundary
  vyperCallOutcome vyperStatePreservation vyperState
Libs
  proofAuditLib
  monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);

(* Proof domain only. Successful oracle payloads may replace the account map;
   every remaining payload therefore carries the same physical supply bound. *)
Definition source_supply_def:
  source_supply (st:evaluation_state) <=>
    accounts_supply_bounded st.accounts /\
    (!os. st.outcomes = SOME os ==> supply_safe_outcomes os)
End

Definition source_supply_action_def:
  source_supply_action
    (action:evaluation_state -> (α + exception) # evaluation_state) <=>
    !st. source_supply st ==> source_supply (SND (action st))
End

Theorem source_supply_action_result:
  source_supply_action action /\ source_supply st /\ action st = (result,post) ==>
  source_supply post
Proof
  simp[source_supply_action_def] >> strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem source_supply_action_return:
  source_supply_action (vyperState$return value)
Proof
  simp[source_supply_action_def, return_def]
QED

Theorem source_supply_action_raise:
  source_supply_action (vyperState$raise error)
Proof
  simp[source_supply_action_def, raise_def]
QED

Theorem source_supply_action_read:
  source_supply_action (\st. vyperState$return (value st) st)
Proof
  simp[source_supply_action_def, return_def]
QED

Theorem source_supply_action_bind:
  source_supply_action first /\
  (!before value mid.
    source_supply before /\ first before = (INL value,mid) ==>
    source_supply_action (next value)) ==>
  source_supply_action (vyperState$bind first next)
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >>
  `source_supply (SND (first before))` by gvs[source_supply_action_def] >>
  Cases_on `first before` >> rename1 `first before = (outcome,mid)` >>
  Cases_on `outcome` >> gvs[bind_def] >>
  rename1 `first before = (INL value,mid)` >>
  qpat_x_assum `!before value mid. _`
    (qspecl_then [`before`, `value`, `mid`] mp_tac) >> simp[] >>
  simp[source_supply_action_def]
QED

Theorem source_supply_action_bind_simple:
  source_supply_action first /\ (!value. source_supply_action (next value)) ==>
  source_supply_action (vyperState$bind first next)
Proof
  strip_tac >> irule source_supply_action_bind >> simp[]
QED

Theorem source_supply_action_ignore_bind:
  source_supply_action first /\ source_supply_action next ==>
  source_supply_action (vyperState$ignore_bind first next)
Proof
  simp[ignore_bind_def, source_supply_action_bind_simple]
QED

Theorem source_supply_action_cond:
  source_supply_action first /\ source_supply_action second ==>
  source_supply_action (if test then first else second)
Proof
  Cases_on `test` >> simp[]
QED

Theorem source_supply_action_try:
  source_supply_action first /\ (!error. source_supply_action (next error)) ==>
  source_supply_action (try first next)
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >>
  `source_supply (SND (first before))` by gvs[source_supply_action_def] >>
  Cases_on `first before` >> rename1 `first before = (outcome,mid)` >>
  Cases_on `outcome` >> gvs[try_def, source_supply_action_def]
QED

Theorem source_supply_action_finally:
  source_supply_action first /\ source_supply_action cleanup ==>
  source_supply_action (finally first cleanup)
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >>
  `source_supply (SND (first before))` by gvs[source_supply_action_def] >>
  Cases_on `first before` >> rename1 `first before = (outcome,mid)` >>
  Cases_on `outcome` >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def] >>
  `source_supply (SND (cleanup mid))` by gvs[source_supply_action_def] >>
  Cases_on `cleanup mid` >> gvs[] >>
  Cases_on `FST (cleanup mid)` >> gvs[]
QED

Theorem source_supply_action_finally_unless_halt:
  source_supply_action first /\ source_supply_action cleanup ==>
  source_supply_action (finally_unless_halt first cleanup)
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >>
  `source_supply (SND (first before))` by gvs[source_supply_action_def] >>
  Cases_on `first before` >> rename1 `first before = (outcome,mid)` >>
  Cases_on `outcome` >>
  TRY (rename1 `INR error` >> Cases_on `error`) >>
  gvs[finally_unless_halt_def, ignore_bind_def, bind_def, return_def, raise_def] >>
  `source_supply (SND (cleanup mid))` by gvs[source_supply_action_def] >>
  Cases_on `cleanup mid` >> gvs[] >>
  Cases_on `FST (cleanup mid)` >> gvs[]
QED

Theorem source_supply_action_identity:
  (!st result post. action st = (result,post) ==> post = st) ==>
  source_supply_action action
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >> Cases_on `action before` >>
  first_x_assum drule >> simp[]
QED

Theorem source_supply_action_exact_frame:
  (!st result post. action st = (result,post) ==>
    post.accounts = st.accounts /\ post.outcomes = st.outcomes) ==>
  source_supply_action action
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >> Cases_on `action before` >>
  first_x_assum drule >> strip_tac >> gvs[source_supply_def]
QED

Theorem source_supply_action_balances:
  (!st result post. action st = (result,post) ==>
    post.outcomes = st.outcomes /\
    !address. (lookup_account address post.accounts).balance =
              (lookup_account address st.accounts).balance) ==>
  source_supply_action action
Proof
  strip_tac >> simp[source_supply_action_def] >>
  qx_gen_tac `before` >> strip_tac >> Cases_on `action before` >>
  rename1 `action before = (result,after)` >>
  qpat_x_assum `!st result post. _`
    (qspecl_then [`before`, `result`, `after`] mp_tac) >>
  simp[] >> strip_tac >>
  `accounts_supply_bounded after.accounts` by
    (irule accounts_supply_decrease >> qexists_tac `before.accounts` >>
     fs[source_supply_def]) >>
  gvs[source_supply_def]
QED

val () = proofAuditLib.check_theory "vyperSourceSupplyDefs";
