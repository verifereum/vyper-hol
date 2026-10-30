(* TOP-LEVEL: source_supply_fields, machine_supply and initial-state bridges. *)
Theory vyperSourceSupplyFields
Ancestors
  vyperSourceSupplyDefs vyperSupplyBoundary vyperInterpreter vyperState
Libs
  proofAuditLib

Theorem source_supply_fields[simp]:
  (source_supply (st with scopes updated_by fs) <=> source_supply st) /\
  (source_supply (st with immutables updated_by fi) <=> source_supply st) /\
  (source_supply (st with tStorage updated_by ft) <=> source_supply st) /\
  (source_supply (st with logs updated_by fl) <=> source_supply st) /\
  (source_supply (st with requests updated_by fr) <=> source_supply st) /\
  (source_supply (st with pending_deletions updated_by fd) <=> source_supply st)
Proof
  simp[source_supply_def]
QED

Theorem source_supply_accounts:
  source_supply st ==> accounts_supply_bounded st.accounts
Proof
  simp[source_supply_def]
QED

Theorem source_supply_accounts_update[simp]:
  source_supply st /\ accounts_supply_bounded accounts ==>
  source_supply (st with accounts := accounts)
Proof
  simp[source_supply_def]
QED

(* Explicit physical domain of call/deployment soundness. This is proof-only;
   executable account checks and account-typing predicates are unchanged. *)
Definition machine_supply_def:
  machine_supply (am:abstract_machine) orc <=>
    accounts_supply_bounded am.accounts /\
    (!os. orc = SOME os ==> supply_safe_outcomes os)
End

Theorem source_supply_initial_state:
  accounts_supply_bounded am.accounts /\
  (!os. orc = SOME os ==> supply_safe_outcomes os) ==>
  source_supply
    (initial_state am scope_list with <|outcomes := orc; requests := request_list|>)
Proof
  simp[source_supply_def, initial_state_def]
QED

Theorem machine_supply_initial_state:
  machine_supply am orc ==>
  source_supply
    (initial_state am scope_list with <|outcomes := orc; requests := request_list|>)
Proof
  simp[machine_supply_def, source_supply_def, initial_state_def]
QED

Theorem machine_supply_without_oracle[simp]:
  machine_supply am NONE <=> accounts_supply_bounded am.accounts
Proof
  simp[machine_supply_def]
QED

Theorem source_supply_initial_state_plain[simp]:
  source_supply (initial_state am scope_list) <=>
  accounts_supply_bounded am.accounts
Proof
  simp[source_supply_def, initial_state_def]
QED

Theorem machine_supply_accounts:
  machine_supply am orc ==> accounts_supply_bounded am.accounts
Proof
  simp[machine_supply_def]
QED

val () = proofAuditLib.check_theory "vyperSourceSupplyFields";
