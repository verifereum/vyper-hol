# DOSSIER: callable_entry_initial_state

PLAN: `semantics/prop/PLAN_callable_entry_initial_state.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | proved |  | E0002 |  |
| C1.3 | proved |  | E0003 |  |
| C1.4 | proved |  | E0004 |  |
| C2 | proved |  | E0005 |  |
| C3 | proved |  | E0006 |  |
| C4 | proved |  | E0007 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 6 steps, 6 tools, 1 holbuild, 308,103 tok (307,408 in, 695 out, 298,240 cached), 335.3s, $0.215810

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 6 steps, 6 tools, 1 holbuild, 308,103 tok (307,408 in, 695 out, 298,240 cached), 335.3s, $0.215810)
  - Removed [local] attribute from bind_arguments_env_scopes_consistent and bind_arguments_scope_well_typed_stmt in vyperTypeStmtSoundnessScript.sml; rebuilt vyperTypeInitialStateTheory. -> Build succeeded, exporting the existing bind_arguments boundary lemmas without duplicating proofs. (`TO_callable_entry_initial_state-20260603T143413Z_m0005_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0006_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0007_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0005_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0006_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0007_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0002`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 5 steps, 6 tools, 1 holbuild, 307,592 tok (306,795 in, 797 out, 285,056 cached), 33.8s, $0.275133

### Attempts / Evidence

- `E0002` (proved, , actual effort: 1 sessions, 1 msgs, 5 steps, 6 tools, 1 holbuild, 307,592 tok (306,795 in, 797 out, 285,056 cached), 33.8s, $0.275133)
  - Added initial_state_accounts_well_typed and initial_state_single_scope_well_typed to vyperTypeInitialStateScript.sml using simp over machine_well_typed_def, initial_state_def, and state_well_typed_def; rebuilt vyperTypeInitialStateTheory. -> Both boundary lemmas proved; target build succeeded (remaining cheats are pre-existing downstream task obligations). (`TO_callable_entry_initial_state-20260603T143413Z_m0016_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0017_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0016_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0017_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 4 steps, 4 tools, 1 holbuild, 284,876 tok (284,177 in, 699 out, 278,016 cached), 32.2s, $0.190783

### Attempts / Evidence

- `E0003` (proved, , actual effort: 1 sessions, 4 steps, 4 tools, 1 holbuild, 284,876 tok (284,177 in, 699 out, 278,016 cached), 32.2s, $0.190783)
  - Added env_context_consistent_empty_static_maps and env_immutables_consistent_empty_static_maps; each closes by simp over env_context_consistent_def/env_immutables_consistent_def with FEMPTY static maps; rebuilt vyperTypeInitialStateTheory. -> Both empty-static-map boundary lemmas proved and target build succeeded. (`TO_callable_entry_initial_state-20260603T143413Z_m0025_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0026_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0025_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0026_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0004`
- blocker: 
- actual effort: 1 sessions, 8 steps, 9 tools, 2 holbuild, 666,536 tok (664,742 in, 1,794 out, 652,288 cached), 77.8s, $0.442234

### Attempts / Evidence

- `E0004` (proved, , actual effort: 1 sessions, 8 steps, 9 tools, 2 holbuild, 666,536 tok (664,742 in, 1,794 out, 652,288 cached), 77.8s, $0.442234)
  - Added functions_well_typed_callable_body_empty_static_maps; unfolded functions_well_typed_def only inside this lemma, specialized fn_sigs and three static maps to FEMPTY, discharged empty-map side conditions by simp, extracted env_body/env_after fields and parameter-map facts. -> Initial proof left two parameter conjunct goals; adding metis_tac after simplification closed them from the function-typing witness assumptions. vyperTypeInitialStateTheory built successfully. (`TO_callable_entry_initial_state-20260603T143413Z_m0036_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0037_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0038_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0039_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0036_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0039_t001` (use `read_tool_output` for exact output)

## C2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0005`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 19 steps, 18 tools, 8 holbuild, 1,867,218 tok (1,862,844 in, 4,374 out, 1,814,656 cached), 178.5s, $1.279488

### Attempts / Evidence

- `E0005` (proved, , actual effort: 1 sessions, 2 msgs, 19 steps, 18 tools, 8 holbuild, 1,867,218 tok (1,862,844 in, 4,374 out, 1,814,656 cached), 178.5s, $1.279488)
  - Replaced main theorem cheat with assembly proof: use functions_well_typed_callable_body_empty_static_maps for env_body/env_after, derive scope_well_typed via exported bind_arguments_scope_well_typed_stmt and args_values_typed_def, instantiate initial_state witnesses, and assemble env_consistent using empty-static-map lemmas plus bind_arguments_env_scopes_consistent. -> After correcting theorem instantiations for bind_arguments lemmas, vyperTypeInitialStateTheory built successfully with the main theorem proved. (`TO_callable_entry_initial_state-20260603T143413Z_m0047_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0048_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0049_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0050_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0058_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0059_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0062_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0063_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0047_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0063_t001` (use `read_tool_output` for exact output)

## C3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0006`
- blocker: 
- actual effort: 1 sessions, 6 steps, 6 tools, 1 holbuild, 332,999 tok (331,799 in, 1,200 out, 322,816 cached), 44.1s, $0.242323

### Attempts / Evidence

- `E0006` (proved, , actual effort: 1 sessions, 6 steps, 6 tools, 1 holbuild, 332,999 tok (331,799 in, 1,200 out, 322,816 cached), 44.1s, $0.242323)
  - Replaced the C3 cheat with a direct `metis_tac` over `callable_entry_establishes_type_soundness_preconditions` and `typed_stmts_no_type_error`. -> The corollary builds cleanly; the main theorem supplies the existential preconditions and typed_stmts_no_type_error discharges the no-TypeError goal. (`TO_callable_entry_initial_state-20260603T143413Z_m0081_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0082_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0081_t001` (use `read_tool_output` for exact output)
- `TO_callable_entry_initial_state-20260603T143413Z_m0082_t001` (use `read_tool_output` for exact output)

## C4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 25 steps, 43 tools, 6 holbuild, 1,972,931 tok (1,969,068 in, 3,863 out, 1,903,488 cached), 231.1s, $1.395534

### Attempts / Evidence

- `E0007` (proved, , actual effort: 1 sessions, 2 msgs, 25 steps, 43 tools, 6 holbuild, 1,972,931 tok (1,969,068 in, 3,863 out, 1,903,488 cached), 231.1s, $1.395534)
  - Witnessed the existential with `empty_evaluation_context`, arbitrary unused `am`, empty typing_env records, and `initial_state initial_machine_state [FEMPTY]`; simplified definitions including empty account and lookup_scopes definitions. -> After adding qualified vfmState/vyperState definitions and using `ARB` for the unused polymorphic existential `am`, holbuild vyperTypeInitialStateTheory succeeded. (`TO_callable_entry_initial_state-20260603T143413Z_m0100_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0101_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0107_t001`, `TO_callable_entry_initial_state-20260603T143413Z_m0112_t001`)

### Evidence refs

- `TO_callable_entry_initial_state-20260603T143413Z_m0112_t001` (use `read_tool_output` for exact output)
