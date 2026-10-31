# STATE_expr_oracle_storage
Updated: 2026-10-29

## Cursor
- component: C1.4
- status: in_progress
- active_file: lowering/exprOracleStoragePreservationScript.sml
- next_action: Read current partial script and add Resume eval_expr_oracle_storage_mutual[Expr_Attribute] before Finalise. Use existing SCC Expr_Attribute proof as interface reference, adding syntactic restrictions and explicit suffix transport. Continue remaining compound-expression/call Resume blocks. C1.1-C1.3 are committed; this partial new script is intentionally untracked/uncommitted until build-clean.
- expected_goal_shape: Latest build verifies every supplied Resume then Finalise fails: No resumption proof found for label Expr_Attribute. Other compound expressions and allowed calls also still lack Resume proofs; frozen consumer cheat remains untouched.
- verify_with: holbuild(targets=["exprOracleStoragePreservationTheory"], timeout=1800)

## If This Fails
- Inspect isolated Resume goal; use existing boundary lemmas and explicit suffix transport. checkpoint_progress for useful partial proofs; if missing semantic helper or structural blockage arises, close_component(stuck) with evidence then plan_oracle review. Do not edit frozen target until helper theorem builds.

## Do Not Retry
- ho_match_mp_tac evaluate_ind with unconstrained polymorphic !cx s. T clauses: Types are not fixed to evaluator domain types; higher-order matching fails safe_insert. Current typed reflexive evaluator clauses match and simplify away.
  - evidence: tool_output:TO_expr_oracle_storage-20261029T191510Z_m0075_t001
- simp[] on complete evaluate_ind antecedent before splitting conjunctions: Aggregate simplification exceeded 2.5s. Current rpt conj_tac before simp[] works.
  - evidence: tool_output:TO_expr_oracle_storage-20261029T191510Z_m0081_t001

## Reflection
### Tunnel Vision Check
- The induction projection is working: target/base places, Pop and both list recursions have checked proofs. No reason yet to change induction variable or definitions.
- Outside-the-box option not pursued: stronger compositional state-predicate boundaries could reduce repeated runtime/oracle transport. A fresh expert should assess this if repeated transport becomes brittle, rather than copying the whole SCC proof.
- Remaining ExtCall slicing and place-typed Len/selection are likely the key integration risks. Do not mistake easy atomic branches for validation of every remaining branch.

### What Went Wrong
- Unconstrained polymorphic True clauses prevented evaluate_ind higher-order matching; typed evaluator reflexive equalities now represent irrelevant predicates.
- simp on the entire induction antecedent timed out; splitting conjuncts first fixed this.
- gvs normalizes call_evaluation_safe premises to [] after empty-call rewriting. A later drule_all of an unsimplified exported typing theorem may need the original syntactic safety assertion reintroduced by simp[].
- Several static failures were missing direct Ancestors imports, not proof-interface failures. Imports now cover all supplied Resume blocks.

### Ignored Signals
- No new counterexample evidence was produced. Oracle call failure/empty-outcome cases were covered generically by checked primitive boundary proofs, not by assuming successful adoption.
- The helper is not yet a complete theorem: Finalise correctly rejects missing resumptions. Do not commit or claim C1.4 proved from the partial build.

### Strategy Adjustments
- Continue one named branch at a time, keeping the verified prefix. Reuse C1.2 oracle boundaries instead of postulated primitive theorems.
- Use oracle_storage_entry_suffix with the relevant eval_outcome_suffix_mutual conjunct (or separate eval_expr_results_outcome_suffix) rather than the old custom ORACLE_STORAGE_TAC.
- C1.1-C1.3 commits: 95f0d587, b0062821, 1e4b5d69. Local PLAN/DOSSIER files were not staged.

### Oracle Feedback
- Strategist accepted all three prerequisite closures without PLAN changes. The oracle-only primitive argument held for arbitrary accounts in eval_ext_call_effects because SOME mode ignores that argument.
- C1.4 is still active; partial progress is recorded in episodes E0004 and E0005, not a terminal closure.

## Evidence Pointers
- tool_output:TO_expr_oracle_storage-20261029T191510Z_m0127_t001 - latest build reaches Finalise missing Expr_Attribute after all supplied Resume proofs pass
- episode:E0005 - latest C1.4 partial checkpoint
- episode:E0004 - induction setup and prior branch evidence
- tool_output:TO_expr_oracle_storage-20261029T191510Z_m0068_t001 - C1.3 review acceptance
- source:lowering/exprOracleStoragePreservationScript.sml - incomplete projected mutual proof with explicit Finalise
