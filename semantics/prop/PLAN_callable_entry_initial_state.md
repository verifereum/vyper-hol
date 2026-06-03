# PLAN

## Structured Components

### C1: Reusable entry-state proof infrastructure
- Kind: `proof_infrastructure`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: All helper facts follow by unfolding existing definitions and by exporting already-proved local argument-binding facts. The only non-mechanical part is keeping the exported interface non-duplicative and aligned with the final theorem use sites.
- Required for completion: yes
- Checkpoint: yes

#### Summary
Build the small reusable interface needed before proving the frozen entry theorem. Export the existing argument-binding facts instead of creating duplicate lemmas. Add boundary lemmas for `initial_state`, empty static maps, and instantiating `functions_well_typed` with empty global maps. These helpers make the final theorem a short assembly proof rather than a long manual unfolding proof.

#### Argument
The key observation is that the frozen theorem does not require the produced `env_body` to use the caller-supplied `bare_globals`, `toplevel_vtypes`, or `flag_members`. Because `functions_well_typed` is quantified over all static maps satisfying its side conditions, instantiate it with the supplied `fn_sigs` but with `FEMPTY` for `bare_globals`, `toplevel_vtypes`, and `flag_members`. Empty maps satisfy the global side conditions trivially and also make `env_context_consistent`/`env_immutables_consistent` trivial. The only runtime-state work is then local: `bind_arguments` creates exactly one scope corresponding to the body environment's parameter variables, and `machine_well_typed` plus `scope_well_typed` gives `state_well_typed (initial_state am [scope])`.

#### Definition design
Do not introduce new semantic definitions. The proof interface should consist of boundary lemmas: (1) argument binding implies `scope_well_typed` under `args_values_typed`; (2) argument binding plus the parameter-variable facts from `functions_well_typed` implies `env_scopes_consistent`; (3) empty static maps imply the context/immutables portions of `env_consistent`; (4) `machine_well_typed` transfers to `initial_state`. Failure sign: if consumers repeatedly unfold `bind_arguments_def`, `env_consistent_def`, or `initial_state_def`, the boundary lemma interface is too weak.

#### Code structure
Keep the target theorem file `semantics/prop/vyperTypeInitialStateScript.sml` as the final assembly layer. Prefer de-localizing the already-proved `bind_arguments_env_scopes_consistent` and `bind_arguments_scope_well_typed_stmt` in `vyperTypeStmtSoundnessScript.sml` so `vyperTypeInitialStateScript.sml` can use them through its existing ancestor; do not duplicate near-identical exported lemmas. Put new entry-specific boundary lemmas near the definitions in `vyperTypeInitialStateScript.sml` before the main theorem unless a separate helper theory is needed by holbuild dependency order.

### C1.1: Expose existing bind_arguments boundary lemmas without duplication
- Kind: `source_cleanup`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: The needed lemmas already exist and are proved locally in vyperTypeStmtSoundnessScript.sml; removing `[local]` from the specific theorem declarations should not change their proofs and avoids duplicate helper statements.

#### Summary
Make the existing argument-binding lemmas available to `vyperTypeInitialStateScript.sml`. Target the local theorems `bind_arguments_env_scopes_consistent` and `bind_arguments_scope_well_typed_stmt`. Do not add duplicate exported versions with different names unless de-localizing demonstrably breaks the build. After this edit, holbuild should expose these names from the `vyperTypeStmtSoundness` ancestor.

#### Approach
In `semantics/prop/vyperTypeStmtSoundnessScript.sml`, remove the `[local]` attribute from exactly the theorems needed by the entry proof: `bind_arguments_env_scopes_consistent` and `bind_arguments_scope_well_typed_stmt`. Their local support lemmas may remain local because the exported theorem objects do not need them at use sites. Build enough to confirm the theory still exports and that `vyperTypeInitialStateScript.sml` can reference the names.

#### Not to try
Do not copy the local bind-argument proof block into `vyperTypeInitialStateScript.sml`; that creates near-duplicate lemmas and violates the task cleanup criterion. Do not unfold `bind_arguments_def` in the final main theorem.

### C1.2: Initial-state runtime well-typedness lemmas
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 10
- Work units: 2
- Rationale: These are direct consequences of `machine_well_typed_def`, `initial_state_def`, `state_well_typed_def`, and the supplied scope well-typedness.
- Dependencies: C1.1

#### Summary
Prove small boundary facts connecting `machine_well_typed` to `initial_state`. These facts should expose accounts and state well-typedness for `initial_state am [scope]`. They will keep the main theorem from manually unpacking record fields.

#### Statement
Suggested outputs:
```sml
Theorem initial_state_accounts_well_typed:
  machine_well_typed am ==>
  accounts_well_typed (initial_state am scs).accounts

Theorem initial_state_single_scope_well_typed:
  machine_well_typed am /\ scope_well_typed scope ==>
  state_well_typed (initial_state am [scope])
```

#### Approach
Unfold `machine_well_typed_def`, `initial_state_def`, `state_well_typed_def`, and simplify list `EVERY`. The second lemma uses the `EVERY` conjunct for `am.immutables` unchanged and the singleton scope list for the new local scope.

#### Not to try
Do not prove a more complicated theorem about arbitrary scope lists unless needed. The frozen theorem only constructs `initial_state am [scope]`.

### C1.3: Empty-static-map env_consistent boundary lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The lemmas are definition-unfolding facts, but the record-field hypotheses must be stated exactly so they match the environment witness returned by `functions_well_typed`.

#### Summary
Prove reusable facts that make `env_context_consistent` and `env_immutables_consistent` trivial when the global/static maps are empty. These facts are central to avoiding dependence on the task's stronger-looking but unnecessary `global_maps_consistent` and `immutables_ready` assumptions. The final theorem should use these lemmas instead of unfolding the consistency definitions repeatedly.

#### Statement
Suggested outputs:
```sml
Theorem env_context_consistent_empty_static_maps:
  env.current_src = current_module cx /\
  env.type_defs = get_tenv cx /\
  env.fn_sigs = fn_sigs /\
  env.bare_globals = FEMPTY /\
  env.toplevel_vtypes = FEMPTY /\
  env.flag_members = FEMPTY /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx ==>
  env_context_consistent env cx

Theorem env_immutables_consistent_empty_static_maps:
  env.bare_globals = FEMPTY /\
  env.toplevel_vtypes = FEMPTY ==>
  env_immutables_consistent env cx st
```

#### Approach
For the context lemma, unfold `env_context_consistent_def` and discharge all `FLOOKUP FEMPTY` cases by simplification; the only nonempty obligations are the fn-signature conjuncts and the field equalities. For the immutables lemma, unfold `env_immutables_consistent_def`; every quantified premise begins with a lookup into an empty map.

#### Not to try
Do not try to derive full `env_context_consistent` from the task's `global_maps_consistent`; that would require layout-slot side conditions not present in `global_maps_consistent_def`. The intended route is to instantiate `functions_well_typed` with empty static maps and build an empty-static-map environment.

### C1.4: Instantiate functions_well_typed at callable entry with empty static maps
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: This is the main abstraction that prevents brittle manual theorem plumbing in the final proof. It follows by unfolding `functions_well_typed_def` and using empty-map simplification for the global side conditions.
- Dependencies: C1.3
- Checkpoint: yes

#### Summary
Package the `functions_well_typed` instantiation needed by the entry theorem. Given the real `fn_sigs` consistency/completeness and a located callable function, produce an `env_body` whose static maps are empty, whose parameter variable maps match `args`, and whose body typing succeeds. This lemma is a checkpoint because if it fails, the whole strategy needs revision.

#### Statement
Suggested output:
```sml
Theorem functions_well_typed_callable_body_empty_static_maps:
  functions_well_typed cx /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) ==>
  ?env_body env_after.
    env_body.current_src = src /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = fn_sigs /\
    env_body.bare_globals = FEMPTY /\
    env_body.toplevel_vtypes = FEMPTY /\
    env_body.flag_members = FEMPTY /\
    type_stmts env_body ret body = SOME env_after /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
```

#### Approach
Unfold `functions_well_typed_def` only inside this lemma. Specialize the outer universal quantifiers with `fn_sigs`, `FEMPTY`, `FEMPTY`, and `FEMPTY`; prove the three static-map side conditions by `simp[FLOOKUP_DEF]`/finite-map simplification. Strip the returned witness and keep only the fields and body-typing facts needed downstream.

#### Not to try
Do not specialize `functions_well_typed` with the task's `bare_globals`, `toplevel_vtypes`, and `flag_members`; those maps are not needed for the frozen conclusion and may not provide `env_context_consistent` layout obligations. Do not expose `ret_tv`, default-expression facts, fallthrough, or nonreentrant facts in this helper unless a later proof actually needs them.

### C2: Prove callable_entry_establishes_type_soundness_preconditions
- Kind: `main_theorem`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: After C1, the proof is an assembly of exported boundary lemmas. The main subtlety is choosing the empty-static-map body environment rather than trying to validate the caller-supplied maps.
- Required for completion: yes
- Dependencies: C1.2, C1.3, C1.4
- Checkpoint: yes

#### Summary
Prove the frozen main theorem exactly as stated. Use `functions_well_typed_callable_body_empty_static_maps` to obtain a typeable `env_body` with empty static maps. Use `bind_arguments_scope_well_typed_stmt` plus `args_values_typed_def` for the entry scope, `bind_arguments_env_scopes_consistent` for scope consistency, and the initial-state lemmas for runtime state/account well-typedness. The assumptions `global_maps_consistent` and `immutables_ready` are not needed on this proof path but remain harmless frozen premises.

#### Statement
```sml
Theorem callable_entry_establishes_type_soundness_preconditions:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  current_module cx = src /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members /\
  immutables_ready bare_globals toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  ?env_body env_after st.
    st = initial_state am [scope] /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body ret body = SOME env_after
```

#### Approach
First obtain `env_body, env_after` from C1.4 using the current callable lookup. Set `st = initial_state am [scope]`. Prove `scope_well_typed scope` from `bind_arguments_scope_well_typed_stmt`; its index premise follows immediately from `args_values_typed_def` and `LENGTH args = LENGTH vals`. Assemble `env_consistent_def` with C1.3 for context/immutables and `bind_arguments_env_scopes_consistent` for scopes; use `current_module cx = src` to rewrite `env_body.current_src = current_module cx`.

#### Not to try
Do not attempt to prove `env_context_consistent` for the task-supplied `bare_globals`, `toplevel_vtypes`, or `flag_members`; that route runs into layout-slot obligations outside the frozen hypotheses. Do not unfold `functions_well_typed_def` in the final theorem; keep that work inside C1.4.

### C3: Prove callable_entry_no_type_error
- Kind: `corollary`
- Risk: 1
- Work priority: 20
- Work units: 2
- Rationale: This is a direct application of the main theorem and existing public soundness theorem `typed_stmts_no_type_error`.
- Required for completion: yes
- Dependencies: C2

#### Summary
Prove the frozen no-TypeError corollary. Reuse the exact assumptions to invoke `callable_entry_establishes_type_soundness_preconditions`. Then apply `typed_stmts_no_type_error` to `eval_stmts cx body (initial_state am [scope])`. No new semantic facts should be needed.

#### Statement
```sml
Theorem callable_entry_no_type_error:
  functions_well_typed cx /\
  context_well_typed cx /\
  machine_well_typed am /\
  current_module cx = src /\
  fn_sigs_consistent fn_sigs cx /\
  fn_sigs_complete fn_sigs cx /\
  global_maps_consistent cx bare_globals toplevel_vtypes flag_members /\
  immutables_ready bare_globals toplevel_vtypes cx am.immutables /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,body) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  args_values_typed (get_tenv cx) args vals ==>
  no_type_error_eval (eval_stmts cx body (initial_state am [scope]))
```

#### Approach
Destructure the existential from C2, rewrite the returned `st = initial_state am [scope]`, and feed `functions_well_typed cx`, `context_well_typed cx`, `accounts_well_typed st.accounts`, `state_well_typed st`, `env_consistent env_body cx st`, and `type_stmts env_body ret body = SOME env_after` to `typed_stmts_no_type_error`. This should be a short `metis_tac`/`drule_all` proof after the main theorem is available.

#### Not to try
Do not use lower-level `eval_stmts_no_type_error` directly unless `typed_stmts_no_type_error` causes a name or ancestor issue. Do not reprove any entry-state invariant here.

### C4: Prove type_soundness_preconditions_satisfiable
- Kind: `corollary`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: The theorem is a concrete non-vacuity witness. It should be straightforward but may require some record-field simplification for empty contexts and machines.
- Required for completion: yes
- Dependencies: C1.2, C1.3

#### Summary
Prove the frozen existential satisfiability corollary with an empty context, empty abstract machine, one empty scope, and an empty static typing environment. The body statement list is `[]`, so `type_stmts env_body NoneT [] = SOME env_body` by definition. The proof should establish `functions_well_typed` vacuously because the empty evaluation context has no module code/callable functions.

#### Statement
```sml
Theorem type_soundness_preconditions_satisfiable:
  ?cx am env_body env_after st.
    functions_well_typed cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body cx st /\
    type_stmts env_body NoneT [] = SOME env_after
```

#### Approach
Use witnesses along these lines: `cx = empty_evaluation_context`, `am = empty_abstract_machine`, `st = initial_state am [FEMPTY]`, and `env_body` with `current_src = NONE`, `type_defs = get_tenv cx`, all variable/static maps empty, and `fn_sigs = FEMPTY`. Prove `scope_well_typed FEMPTY`, apply C1.2 for `state_well_typed`, apply C1.3 plus direct empty-scope simplification for `env_consistent`, and simplify `type_stmts_def` on `[]`. For `functions_well_typed empty_evaluation_context`, unfold `functions_well_typed_def`, `get_module_code_def`, and `empty_evaluation_context_def`; no callable lookup obligation should survive because there is no module code.

#### Not to try
Do not try to derive this corollary from the main callable-entry theorem; the main theorem needs an actual callable lookup and argument binding, while this existential only needs the core soundness preconditions for an empty statement list.
