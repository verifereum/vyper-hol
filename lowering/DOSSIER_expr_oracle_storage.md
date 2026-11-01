# DOSSIER: expr_oracle_storage

PLAN: `lowering/PLAN_expr_oracle_storage.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | proved |  | E0002 |  |
| C1.3 | proved |  | E0003 |  |
| C1.4 | proved |  | E0007 |  |
| C1.5 | proved |  | E0008 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 3 holbuild, 1,863,625 tok (1,861,346 in, 2,279 out, 1,810,944 cached), 349.0s, $0.3046884

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 3 holbuild, 1,863,625 tok (1,861,346 in, 2,279 out, 1,810,944 cached), 349.0s, $0.3046884)
  - Inventory traversal, internal-call collection, suffix and runtime preservation interfaces; add only list-negation/empty collection and combined oracle entry transport facts. -> exprOracleStorageInterfacesTheory builds. Constructor target inheritance is already definitional; EVERY interfaces allow standard member/TAKE/DROP reasoning without bespoke slicing lemmas. Existing eval_outcome_suffix_mutual plus separate eval_expr_results_outcome_suffix cover all five recursive entries. (`TO_expr_oracle_storage-20261029T191510Z_m0030_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0031_t001`)
  - Remove [local] from six runtime-consistency boundary lemmas, retaining all their statements and proofs. -> vyperTypeEvalStoragePreservationTheory rebuilt cleanly; place-typed expression lemma explicitly accepts well_typed_expr or type_place_expr. (`TO_expr_oracle_storage-20261029T191510Z_m0026_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0030_t001`)

### Evidence refs

- `TO_expr_oracle_storage-20261029T191510Z_m0030_t001` (use `read_tool_output` for exact output)
- `TO_expr_oracle_storage-20261029T191510Z_m0031_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0002`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 10 steps, 9 tools, 2 holbuild, 795,800 tok (794,306 in, 1,494 out, 774,656 cached), 128.3s, $0.1317056

### Attempts / Evidence

- `E0002` (proved, , actual effort: 1 sessions, 1 msgs, 10 steps, 9 tools, 2 holbuild, 795,800 tok (794,306 in, 1,494 out, 774,656 cached), 128.3s, $0.1317056)
  - Add oracle-only send/effects/extcall wrappers following primitive monadic decomposition; exclude NONE outcomes before unfolding. -> All three boundaries build without postulates; effects quantifies accounts freely because oracle branch ignores accounts. Exported unchanged adopt_call_outcome_INR_storage for failure cases. Initial missing ancestor imports fixed by adding vyperState and vyperMisc. (`TO_expr_oracle_storage-20261029T191510Z_m0047_t001`)

### Evidence refs

- `TO_expr_oracle_storage-20261029T191510Z_m0047_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 13 steps, 12 tools, 1 holbuild, 1,175,499 tok (1,174,477 in, 1,022 out, 1,151,232 cached), 137.4s, $0.1718332

### Attempts / Evidence

- `E0003` (proved, , actual effort: 1 sessions, 1 msgs, 13 steps, 12 tools, 1 holbuild, 1,175,499 tok (1,174,477 in, 1,022 out, 1,151,232 cached), 137.4s, $0.1718332)
  - Inspect typed Pop SCC branch and pop_place_preserves_contract_storage premises; expose existing target success typing lemma unchanged. -> Existing pop theorem already directly consumes contract storage, layout, region and dynamic array runtime typing. eval_target_place_success_storage_type and eval_target_place_region supply these facts; no duplicate pop lemma needed. (`TO_expr_oracle_storage-20261029T191510Z_m0056_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0058_t001`)
  - Inspect RawLog/RawRevert/SelfDestruct branches; export existing logs frame and transfer-value storage preservation unchanged. -> All three relevant theories rebuild cleanly. RawRevert does not mutate state after argument evaluation; RawLog uses logs frame; SelfDestruct uses transfer_value preservation. Existing read/selection state frame facts remain available. (`TO_expr_oracle_storage-20261029T191510Z_m0059_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0066_t001`)

### Evidence refs

- `TO_expr_oracle_storage-20261029T191510Z_m0066_t001` (use `read_tool_output` for exact output)
- `TO_expr_oracle_storage-20261029T191510Z_m0056_t001` (use `read_tool_output` for exact output)
- `TO_expr_oracle_storage-20261029T191510Z_m0058_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 5 msgs, 73 steps, 72 tools, 22 holbuild, 5,994,782 tok (5,983,151 in, 11,631 out, 5,862,400 cached), 1633.0s, $0.9440520

### Attempts / Evidence

- `E0004` (progressed, other, actual effort: 1 sessions, 4 msgs, 53 steps, 52 tools, 17 holbuild, 6,102,519 tok (6,094,313 in, 8,206 out, 6,011,904 cached), 864.1s, $0.8480684)
  - Construct restricted evaluate_ind projection in exprOracleStoragePreservationScript.sml with named suspended branches; tautological evaluator clauses enforce types for irrelevant predicates. -> Induction skeleton validates. Plain polymorphic True clauses failed HO matching; typed tautologies work. Split conjunction before simp to avoid aggregate tactic timeout. (`TO_expr_oracle_storage-20261029T191510Z_m0081_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0089_t001`)
  - Prove target wrapper, four base-place branches, four excluded call branches, empty lists/results, typed Pop and captured-results cons. -> All supplied Resume blocks verify; latest build reaches Finalise and fails solely for missing Exprs_cons resumption (other expression cases remain to supply). Base_SubscriptTarget and Results_cons validate explicit oracle_storage_entry_suffix transport without custom assumption scanning. Pop needs reintroducing syntactic call safety after gvs normalizes it to []. (`TO_expr_oracle_storage-20261029T191510Z_m0112_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0119_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0124_t001`)
- `E0005` (progressed, other, actual effort: 1 sessions, 4 msgs, 56 steps, 55 tools, 18 holbuild, 6,504,984 tok (6,495,369 in, 9,615 out, 6,407,936 cached), 950.6s, $0.9118096)
  - Prove Exprs_cons with explicit suffix transport and four atomic expression cases via state frames. -> All new Resume blocks pass. Latest build fails only at Finalise because Expr_Attribute lacks a resumption; this is the next missing branch, not a tactic failure. Unfinished helper theorem remains uncommitted and isolated from the frozen target. (`TO_expr_oracle_storage-20261029T191510Z_m0127_t001`)
- `E0006` (progressed, other, actual effort: 1 sessions, 3 msgs, 41 steps, 40 tools, 12 holbuild, 2,872,719 tok (2,866,467 in, 6,252 out, 2,793,344 cached), 810.3s, $0.4881004)
  - Added Attribute, Builtin (Len and ordinary), RawLog, RawRevert, SelfDestructTarget, Subscript and Send resumptions. -> All supplied resumptions now check; Finalise reports next missing Expr_IfExp. Subscript combines value/place typing branches and explicit suffix transport; Send uses oracle-only primitive boundary. (`TO_expr_oracle_storage-20261029T191510Z_m0173_t001`)
- `E0007` (proved, , actual effort: 1 sessions, 5 msgs, 73 steps, 72 tools, 22 holbuild, 5,994,782 tok (5,983,151 in, 11,631 out, 5,862,400 cached), 1633.0s, $0.9440520)
  - Complete restricted evaluate_ind projection with all named resumptions; transport oracle suffix at sequential entries and use oracle Send/ExtCall boundaries. -> exprOracleStoragePreservationTheory builds cleanly with Finalise registering the complete mutual theorem. Exposed two existing local helpers unchanged. ExtCall handles captured results and keyword slices; no storage postulates used. (`TO_expr_oracle_storage-20261029T191510Z_m0206_t001`)

### Evidence refs

- `TO_expr_oracle_storage-20261029T191510Z_m0206_t001` (use `read_tool_output` for exact output)

## C1.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0008`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 18 steps, 17 tools, 2 holbuild, 2,063,289 tok (2,062,212 in, 1,077 out, 2,046,208 cached), 170.3s, $0.2473988

### Attempts / Evidence

- `E0008` (proved, , actual effort: 1 sessions, 1 msgs, 18 steps, 17 tools, 2 holbuild, 2,063,289 tok (2,062,212 in, 1,077 out, 2,046,208 cached), 170.3s, $0.2473988)
  - Import validated mutual machinery and discharge frozen theorem from expression projection. -> Requested exprStoragePreservationTheory build succeeds; git diff confirms statement untouched. Generated target dat records DISK_THM only; grep of generated Theory.dat files finds no CHEAT/oracle markers. No Theory.txt indexes are generated in this build layout, so audited generated data instead. (`TO_expr_oracle_storage-20261029T191510Z_m0218_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0226_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0228_t001`, `TO_expr_oracle_storage-20261029T191510Z_m0229_t001`)

### Evidence refs

- `TO_expr_oracle_storage-20261029T191510Z_m0218_t001` (use `read_tool_output` for exact output)
- `TO_expr_oracle_storage-20261029T191510Z_m0226_t001` (use `read_tool_output` for exact output)
- `TO_expr_oracle_storage-20261029T191510Z_m0228_t001` (use `read_tool_output` for exact output)
- `TO_expr_oracle_storage-20261029T191510Z_m0229_t001` (use `read_tool_output` for exact output)
