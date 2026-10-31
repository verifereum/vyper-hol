# PLAN

## Structured Components

### C1: Postulate-free oracle expression storage preservation
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The existing SCC proof supplies the typed mutation argument; only send and external-call effects require new oracle-specific boundaries. Internal calls and raw/create branches are syntactically impossible.
- Required for completion: yes

#### Summary
Prove exactly the frozen theorem without either protected-storage postulate. First validate reusable syntax, state-transport, and oracle-call machinery. Then prove an expression-only projection of the evaluator induction, including places and captured argument results. Only after that machinery builds, replace the target cheat and audit the requested build.

#### Not to try
Do not derive protected_storage_calls_preserve from oracle_storage_ok: the former quantifies over real EVM executions. Do not assume expressions are storage-frame operations: Pop mutates storage. Do not assume outcomes stay equal: external calls consume them. Do not start editing the frozen theorem proof before all helper components have been validated.

#### Argument
Use evaluate_ind with nontrivial predicates only for eval_expr, eval_exprs, eval_expr_results, eval_base_place and eval_target_place; instantiate statement, loop and assignment predicates with True. The expression predicate must support both well_typed_expr and type_place_expr, as in eval_scc_storage_preservation_results_mutual, because Len and selection evaluate places. Require empty internal-call lists, absence of expr_evm_run_root throughout the relevant syntax, IS_SOME outcomes, and oracle_storage_ok at each recursive entry. Recursive evaluation preserves oracle mode and oracle validity by outcome suffix; existing typing preservation reconstructs runtime_storage_consistent once the IH supplies storage well-formedness. Pop uses the existing typed place-mutation preservation argument. Send and ExtCall use successful oracle adoption rather than EVM preservation postulates; errors preserve the last well-formed state. IntCall, RawCallTarget, RawCallCalldataTarget and CreateTarget close by contradiction before inspecting their operational bodies.

#### Definition design
Do not alter interpreter, typing, traversal, oracle or storage definitions. Use supported_expr_exists and its companion list/target traversals as the syntactic interface, with EVERY formulations for lists. Avoid introducing an additional recursive admissibility predicate. Validate list slicing and target-index inheritance before induction, and validate that outcome suffix transports SOME mode even for SOME []. New call boundaries should quantify over arbitrary result, including failure, and require only storage well-formedness, oracle validity and oracle mode where sufficient.

#### Code structure
Put generic oracle call boundaries in a semantics-level helper theory importing vyperCallOutcomeStorage and needed preservation theories, or in the existing oracle storage theory if no dependency cycle results. Put traversal bridges in supportedExprTraverse when independent of typing, otherwise in a lowering helper theory. Put the restricted mutual preservation theorem in a new lowering helper theory imported by exprStoragePreservation; keep the frozen theorem script a thin consumer. Expose needed local lemmas from vyperTypeEvalStoragePreservation by removing only [local], preserving statements and proofs. Do not copy the old SCC proof wholesale or alter its theorem statements.

### C1.1: Validate recursive-entry syntax and state interfaces
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Traversal inheritance is structural list reasoning; oracle state transport already has suffix theorems. This exposes the interfaces needed by every recursive call.
- Checkpoint: yes

#### Summary
Inventory existing helpers before adding anything. Validate no-internal-call and no-EVM-run inheritance for expressions, places, lists and list slices. Validate oracle-mode and oracle-validity transport for all five relevant evaluator functions. Export existing local typing/frame lemmas only where consumers actually need them.

#### Statement
Required interfaces: negative supported_exprs_exists is equivalent to EVERY (\e. ~supported_expr_exists p e); this property and int_calls_exprs es = [] pass to TAKE, DROP and members, including HD under nonemptiness. MAP SND fields has the corresponding field property. SubscriptTarget passes the target restriction and expression restriction to its children. outcome_suffix st.outcomes st'.outcomes /\ IS_SOME st.outcomes ==> IS_SOME st'.outcomes. Combine this with oracle_storage_ok_suffix at recursive evaluation boundaries. Reuse existing statements when these outputs already exist.

#### Approach
Use supported_exprs_exists_every and supported_fields_exists_every, constructor equations and int_calls definitions; do not add specialized duplicates of general list facts. Inspect outcome_suffix_modes and eval_outcome_suffix_mutual, including the eval_expr_results conjunct, and prove only missing boundary facts. Export eval_expr_preserves_runtime_consistent, eval_expr_place_preserves_runtime_consistent, list/results and base-place variants as needed with their existing statements/proofs unchanged; build the helper theories.

#### Not to try
Do not duplicate the traversal recursion or introduce custom assumption-scanning ML to transport oracle facts. Do not claim a typing lemma applies to place-typed expressions until its actual premise has been checked.

### C1.2: Oracle-only send and external-call boundaries
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The SOME branch uses already-proved take/adopt storage lemmas; the NONE branch is excluded. Existing postulated helper proofs identify the required monadic case splits.
- Dependencies: C1.1
- Checkpoint: yes

#### Summary
Prove storage preservation for eval_send, eval_ext_call_effects and eval_ext_call in oracle mode. These boundaries handle both success and failure and do not require protected-storage hypotheses. Reuse atomic take/adopt lemmas, including computed-precompile snapshots and non-adoption failures. Build these boundaries before evaluator induction.

#### Statement
For each of eval_send cx has_gas vs, eval_ext_call cx static skip_check sig opts vs, and eval_ext_call_effects cx target calldata value_opt gas accounts: contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\ IS_SOME st.outcomes /\ operation st = (res,st') ==> contract_storage_well_formed cx st'. For effects, quantify accounts freely if the SOME branch ignores that parameter; otherwise retain the actual caller's st.accounts parameter, after inspecting the definition.

#### Approach
Split outcomes first and eliminate NONE; unfold only these primitive wrappers, not evaluate_def. Apply take_call_outcome_storage_suffix and take_adopt_call_outcome_storage_suffix to the oracle branches; expose and reuse adopt_call_outcome_INR_storage for failures. Treat decoding, static-mode restoration and logs through existing frame facts; the proof must cover malformed arguments, empty outcomes, failed outcomes and computed precompiles.

#### Not to try
Do not use eval_send_storage_preserved or eval_ext_call_storage_preserved as black boxes, since their premises include the forbidden postulate. Do not infer successful payload safety from runtime balance/code checks.

### C1.3: Validate typed mutation and non-EVM primitive boundaries
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: The existing Expr_Pop and ordinary-call SCC branches already establish the necessary local facts without relying on real EVM execution.
- Dependencies: C1.1
- Checkpoint: yes

#### Summary
Make the typed Pop boundary available for the restricted induction. Validate storage-frame use for reads, selection, raw logs, raw revert and selfdestruct balance transfer. Reuse existing lemmas in their most general form; only missing consumer-shaped boundaries are new work. This closes the non-oracle mutation portion of the machinery before integration.

#### Statement
Required output is a usable typed Pop continuation: given the existing typed-place and runtime/storage facts at a successful eval_target_place result, pop_place preserves contract_storage_well_formed for arbitrary result. Reuse pop_place_preserves_contract_storage rather than restating it. Expose any necessary existing local frame and result-typing facts from the SCC script unchanged; add only genuinely missing continuation boundaries.

#### Approach
Inspect the actual premises of pop_place_preserves_contract_storage and the proof of Expr_Pop in the existing SCC theorem; package the typed target result facts at the caller boundary if necessary. Similarly inspect ordinary call branches and reuse storage-frame lemmas for logs and balance transfer. Build and validate these interfaces independently of the new recursive theorem.

#### Not to try
Do not characterize Pop as a backend frame. Do not add blanket storage preservation for untyped writes. Do not repair unrelated statement/assignment proofs.

### C1.4: Restricted evaluator mutual preservation machinery
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 13
- Rationale: With call and mutation boundaries validated, the remaining proof follows the existing evaluate_ind shape; excluded branches need no body/loop induction.
- Dependencies: C1.1, C1.2, C1.3
- Checkpoint: yes

#### Summary
Prove the five-function restricted mutual theorem before touching the target proof. Retain both value-typing and place-typing expression cases. Cover captured expression results and target indices, not merely eval_exprs. Validate every branch and build the helper theory postulate-free.

#### Statement
Use the eval_expr, eval_exprs, eval_base_place, eval_target_place and eval_expr_results clauses of eval_scc_storage_preservation_results_mutual as templates, removing both protected-storage premises and adding IS_SOME st.outcomes, empty internal-call lists, and absence of expr_evm_run_root in the appropriate expression/list/target traversal. Preserve runtime_storage_consistent, functions_well_typed, call_evaluation_safe and oracle_storage_ok premises. The expression clause concludes both (well_typed_expr env e ==> contract_storage_well_formed cx st') and (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st'). Other clauses keep their corresponding typing premises and storage conclusion. All other evaluate_ind predicates are True.

#### Approach
Apply evaluate_ind with these predicates and use named Suspend/Resume branches if needed. At each sequential evaluation, use its IH for storage, existing typing preservation for runtime consistency, and suffix transport for oracle premises before invoking the next IH; use list-slice interfaces for ExtCall's target, captured arguments and keyword arguments. Eliminate forbidden call roots syntactically; handle ordinary constructors by frames, Pop by the validated mutation boundary, and Send/ExtCall by C1.2.

#### Not to try
Do not prove the full statement/loop SCC again. Do not use an expression-only value-typing IH: Len and place selection need the place-typing alternative. Do not copy postulated helper applications into the new proof or unfold all evaluator definitions globally. If a new semantic helper is needed, escalate rather than hide an unofficial work queue in this component.

### C1.5: Discharge frozen theorem and certify requested build
- Kind: `proof`
- Risk: 1
- Work priority: 40
- Work units: 2
- Rationale: After the validated mutual theorem, the frozen statement is its value-typed expression projection; final checking is mechanical.
- Dependencies: C1.4
- Checkpoint: yes

#### Summary
Only now replace the cheat in exprStoragePreservationScript.sml. Keep the frozen statement byte-for-byte logically unchanged and derive it from the restricted mutual theorem. Run the requested holbuild target and audit its dependency closure for admissions and statement changes. Report any falsehood only with a checked HOL4 counterexample, never by weakening the task.

#### Statement
eval_expr_oracle_preserves_contract_storage_well_formed exactly as specified in lowering/TASK_expr_oracle_storage.md.

#### Approach
Import the validated helper theory and select its expression/value-typing conclusion with a short direct proof. Run holbuild -j4 build exprStoragePreservationTheory from the project root, requiring zero CHEAT warnings and zero FAILs; audit no new axioms, no modified existing statements, and no duplicate helpers. Use only holbuild, keep the default tactic timeout, and split slow steps rather than raising it.

#### Not to try
Do not begin this leaf while helper builds or checkpoint validation remain unresolved. Do not change assumptions, definitions or the theorem statement to make the final application fit; do not use TRY/ORELSE around search tactics.
