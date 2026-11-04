# TASK: Repair physical source properties after ghost storage observations

## Meta
- Scope is the following existing source-property theories, and this task file:
- semantics/prop/vyperStoragePlaceProvenanceScript.sml
- semantics/prop/vyperEvalOutcomeSuffixScript.sml
- semantics/prop/vyperLookupStorageScopesScript.sml
- semantics/prop/vyperTypeContractGetterScript.sml
- semantics/prop/vyperStorageReadSoundnessScript.sml
- semantics/prop/vyperTypeStatePreservationScript.sml
- semantics/prop/vyperTargetPlaceWriteScript.sml
- semantics/prop/vyperPlaceResultTypingScript.sml
- semantics/prop/vyperTypeExternalCallMachineScript.sml
- semantics/prop/vyperTypeContractSoundnessScript.sml
- semantics/prop/vyperReadOnlyTargetsScript.sml
- semantics/prop/vyperHashMapPreservationScript.sml
- semantics/prop/vyperTypeConstantFoldScript.sml
- semantics/prop/vyperPlaceTypingScript.sml
- semantics/prop/vyperHashMapScript.sml
- semantics/prop/vyperTypeEvalStoragePreservationScript.sml
- semantics/prop/vyperLogPreservationScript.sml
- semantics/prop/vyperExprNoControlScript.sml
- semantics/prop/vyperTypeEvalSoundnessScript.sml
- semantics/prop/vyperHashMapStorageScript.sml
- semantics/prop/vyperStorageFrameScript.sml
- semantics/prop/vyperTypeGlobalLookupSoundnessScript.sml
- semantics/prop/vyperEvalPreservesScopesScript.sml
- semantics/prop/vyperMachineFrameScript.sml

- Do not edit state, interpreter, call-oracle, creation, compiler or other source
  definitions. A separate prover owns vyperStorageTraceScript.sml.
- Owner is concurrently migrating compiler interfaces; leave all lowering files
  and other owner edits untouched. Commit only the permitted files.

## Theorem Statement (FROZEN)
All existing theorem statements in the scope above are frozen exactly as written.
The trace-aware replacements for the exact-state equations are:
```sml
Theorem current_storage_read_result_typed:
  contract_storage_well_formed cx st /\
  storage_var_info cx mid n = SOME (b,off,tv) ==>
  ?ref v observations. lookup_global cx mid n st =
          (INL ref,st with storage_trace := observations) /\
          read_result cx ref st = (INL v,st) /\
          value_has_type tv v

Theorem lookup_global_toplevel_ready:
  FLOOKUP env.toplevel_vtypes (src,id) = SOME vt /\
  env_consistent env cx st ==>
  ?pv observations. lookup_global cx src id st =
         (INL pv,st with storage_trace := observations) /\
       eval_result_typed (env,cx,st) pv vt

Theorem acquire_nonreentrant_lock_eq:
  acquire_nonreentrant_lock addr slot is_view st =
    if lookup_storage (n2w slot)
         (lookup_transient_storage addr st.tStorage) = 1w then
      (INR (Error (RuntimeError "nonreentrant lock")),
       st with storage_trace := st.storage_trace ++ [StorageLock slot])
    else if is_view then
      (INL (),st with storage_trace := st.storage_trace ++ [StorageLock slot])
    else
      (INL (),
       st with <|tStorage updated_by
         update_transient_storage addr
           (update_storage (n2w slot) 1w
             (lookup_transient_storage addr st.tStorage));
         storage_trace := st.storage_trace ++ [StorageLock slot]|>)

Theorem release_nonreentrant_lock_eq:
  release_nonreentrant_lock addr slot st =
    (INL (),
     st with <|tStorage updated_by
       update_transient_storage addr
         (update_storage (n2w slot) 0w
           (lookup_transient_storage addr st.tStorage));
       storage_trace := st.storage_trace ++ [StorageLock slot]|>)

Theorem select_result_hashmap_leaf:
  evaluate_type (get_tenv cx) t = SOME tv ==>
  select_result cx ty (HashMapRef tr slot kt (Type t)) (ValueSubscript kv) st =
  (INL (PlaceR (StoragePlace tr (hashmap_slot slot (encode_hashmap_key kt kv)) tv)),
   st with storage_trace := st.storage_trace ++
     [StorageRoot tr (w2n (hashmap_slot slot (encode_hashmap_key kt kv))) tv])

Theorem select_projection_subscript_sound[local]:
  !env cx st bp bvt ct ie out idx res st'.
  env_consistent env cx st /\ state_well_typed st /\
  eval_result_typed (env,cx,st) bp bvt /\ live_memory_result st bp /\
  well_formed_vtype env.type_defs bvt /\ vtype_annotation_ok bvt ct /\
  subscript_vtype bvt (expr_type ie) = SOME out /\
  value_runtime_typed env (expr_type ie) idx /\
  select_result cx ct bp (ValueSubscript idx) st = (res,st') ==>
  st' = st with storage_trace := st'.storage_trace /\ no_type_error_result res /\
  (case res of INL pv => eval_result_typed (env,cx,st') pv out | INR _ => T)
```
Do not modify this statement. Prove it as-is, or produce a counterexample.
This restriction covers every pre-existing theorem in the scoped files. No
new or stronger premise, new admission or dropped result is permitted.

## Completion Criteria
- Repair proof bodies in the scoped theories and build the targets below.
- Preserve every existing definition and theorem statement byte for byte.
- Search existing theorems before adding a helper. Reuse/export existing useful
  facts instead of adding local copies. Add helpers only for actual consumers.
- If another unchanged exact-state statement is false under instrumentation,
  report its counterexample and stop rather than inventing a premise.
- Commit only the scoped source files and task file; never push. Every commit
  ends with Bot: sol (OpenAI GPT-6.1 Sol).

## Build
`holbuild -j4 build vyperStoragePlaceProvenanceTheory vyperEvalOutcomeSuffixTheory vyperLookupStorageScopesTheory vyperTypeContractGetterTheory vyperStorageReadSoundnessTheory vyperTypeStatePreservationTheory vyperTargetPlaceWriteTheory vyperPlaceResultTypingTheory vyperTypeExternalCallMachineTheory vyperTypeContractSoundnessTheory vyperReadOnlyTargetsTheory vyperHashMapPreservationTheory vyperTypeConstantFoldTheory vyperPlaceTypingTheory vyperHashMapTheory vyperTypeEvalStoragePreservationTheory vyperLogPreservationTheory vyperExprNoControlTheory vyperTypeEvalSoundnessTheory vyperHashMapStorageTheory vyperStorageFrameTheory vyperTypeGlobalLookupSoundnessTheory vyperEvalPreservesScopesTheory vyperMachineFrameTheory`
The owner checked the producer and primitive state/scope/place frames. The full
batch has not built yet; the four changed statements above have not all parsed
because the same migration is needed in ancestors. Their old proofs remain.

## Background
Storage observation logging changes only evaluation_state.storage_trace.
lookup_global, set_global and final hashmap extend_place append StorageRoot;
lock helpers append StorageLock, including failed/view checks. take/adopt
operations append consumed outcomes and effective backend snapshots. Failed
CREATE retains its actual adoption. Existing physical type, range, scope,
immutables, account, log, oracle suffix and provenance properties must survive.
A mechanical first pass unfolds ignore_bind and record_storage_event at direct
primitive consumers. The remaining work is proof transport, not a new invariant.

## Domain Constraints
- Default 2.5s tactic timeout, no override/bypass. No TRY/ORELSE around search.
- No cheat, axioms, new admissions, stronger hypotheses or hidden restrictions.
- Do not change executable definitions or erase observations from producer runs.
- Never invoke holbuild run/repl, Holmake or a full CI/bytecode parity build.
- Build only edited theories above; dependencies replay automatically.

## Available Resources
- semantics/vyperStateScript.sml: logging, primitive erasure, actual global/map
  lookup equations and evaluation_state record.
- semantics/vyperInterpreterScript.sml: actual lock and evaluator definitions.
- semantics/prop/vyperStatePreservationScript.sml: lookup_global_state frames
  only storage_trace; project physical fields using record component equality.
- semantics/prop/vyperPlaceFramesScript.sml: extend_place_state and
  select_result_state frame only storage_trace.
- semantics/prop/vyperStorageBackendScript.sml: get_storage_storage_trace,
  get_storage_backend_storage_trace and set_storage_backend_storage_trace.
- semantics/prop/vyperScopePreservationScript.sml and
  semantics/prop/vyperImmutablesPreservationScript.sml: checked primitive frames.
- semantics/prop/vyperCallOutcomeFrameScript.sml: generic R transport requires
  closure under arbitrary result-side storage_trace updates; locals kit includes
  the logger primitives. No new public closure assumption may be added here.

## Notes
The finite public storage contract and lowering horizon parameter are separate
owner work. This task must preserve the independently meaningful existing global
storage theorems; it does not prove the new finite end-to-end theorem.
