# TASK: Preserve oracle transport through storage ghost traces

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

The following seven statements are frozen. Do not modify these statements.
Prove them as-is, or produce a counterexample. Preserve every other existing
statement and every executable definition. Existing proofs remain in place,
including any currently failing proofs.

In `semantics/prop/vyperCallOutcomeFrameScript.sml`:

```sml
Theorem take_call_outcome_transport:
  (!s t observations. R s t ==> R s (t with storage_trace := observations)) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  take_call_outcome target calldata value_opt st = (res,st') ==>
  R st st'
```

In `semantics/prop/vyperCallOutcomeFrameScript.sml`:

```sml
Theorem adopt_call_outcome_transport:
  (!s t observations. R s t ==> R s (t with storage_trace := observations)) /\
  (!s. R s s) /\
  (!s accounts transient logs pending.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs; pending_deletions := pending|>)) /\
  adopt_call_outcome rq outcome st = (res,st') ==>
  R st st'
```

In `semantics/prop/vyperCallOutcomeFrameScript.sml`:

```sml
Theorem checked_call_outcome_transport:
  (!s t observations. R s t ==> R s (t with storage_trace := observations)) /\
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs pending.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs; pending_deletions := pending|>)) /\
  (!bs s res t. k bs s = (res,t) ==> R s t) /\
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==>
  R st st'
```

In `semantics/prop/vyperCallOutcomeFrameScript.sml`:

```sml
Theorem ExtCall_outcome_transport:
  (!s t observations. R s t ==> R s (t with storage_trace := observations)) /\
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs pending.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs; pending_deletions := pending|>)) /\
  (!bs s res t. k bs s = (res,t) ==> R s t) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==>
  R st st'
```

In `semantics/prop/vyperCallOutcomeFrameScript.sml`:

```sml
Theorem Send_outcome_transport:
  (!s t observations. R s t ==> R s (t with storage_trace := observations)) /\
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs pending.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs; pending_deletions := pending|>)) /\
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  R st st'
```

In `semantics/prop/vyperCallOutcomeFrameScript.sml`:

```sml
Theorem take_adopt_call_outcome_effects:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  ?os rest prefix.
    st.outcomes = SOME os /\ st2.outcomes = SOME rest /\
    os = prefix ++ rest /\ LENGTH prefix <= 1 /\
    rq = call_outcome_request target calldata value_opt st /\
    st2.requests = record_request rq st.requests /\
    st2 = st with <|outcomes := SOME rest;
                   requests := record_request rq st.requests;
                   accounts := st2.accounts; tStorage := st2.tStorage;
                   logs := st2.logs; pending_deletions := st2.pending_deletions;
                   storage_trace := st2.storage_trace|> /\
    (outcome.co_success /\ ~rq.cr_static ==>
      st2.accounts = outcome.co_accounts /\
      st2.tStorage = outcome.co_tStorage /\
      st2.logs = st.logs ++ outcome.co_logs /\
      accounts_runtime_well_typed st2.accounts) /\
    (rq.cr_static \/ ~outcome.co_success ==>
      st2.accounts = st.accounts /\ st2.tStorage = st.tStorage /\
      st2.logs = st.logs) /\
    (computed_precompile rq ==> prefix = [] /\ st2.requests = st.requests)
```

In `semantics/prop/vyperCallOutcomeBranchesScript.sml`:

```sml
Theorem checked_call_outcome_success_frame:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  rq.cr_accounts = st.accounts /\ rq.cr_tStorage = st.tStorage /\
  st2 = st with <|accounts := st2.accounts; tStorage := st2.tStorage;
                 logs := st2.logs; outcomes := st2.outcomes;
                 requests := st2.requests; pending_deletions := st2.pending_deletions;
                 storage_trace := st2.storage_trace|>
```

## Completion Criteria

1. `holbuild -j4 build vyperCallOutcomeFrameTheory` passes at the default
   tactic limit, with no new admissions or axioms.
2. Existing theorem statements and definitions outside the frozen seven are
   unchanged. Added proof helpers must be independently sound and reusable.
3. No duplicate lemmas, timeout overrides, or TRY/ORELSE around proof search.
4. Edit only the two files holding these statements. Other source files have
   owner work in progress and must remain untouched.

## Build

```sh
holbuild -j4 build vyperCallOutcomeFrameTheory
```

## Background

Evaluation state now has an append-only storage_trace ghost field. Taking an
outcome records StorageOutcome before account validation; adopting a backend
records StorageBackend, including failed creation. Generic frame relations may
observe arbitrary fields, so the five transport contracts explicitly require
closure under changes to the result's ghost trace. The exact two state-frame
conclusions expose their actual resulting storage_trace. Physical source
behavior and all existing non-ghost assumptions are fixed.

## Domain Constraints

No new cheats or admissions, universal crypto hypotheses, runtime restrictions,
new error exemptions, or changed executable definitions. No new strengthened
hypotheses. Keep default 2.5s tactic timeout; never wrap proof search in TRY or
ORELSE. Use holbuild build, never run/repl/Holmake. Preserve inherited admissions
outside scope. Do not edit the owner's interpreter/create/finite-contract work.
Do not push. Commit only your allowed source changes and use the trailer
`Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- semantics/prop/vyperCallOutcomeFrameScript.sml: target transport contracts.
- semantics/prop/vyperCallOutcomeBranchesScript.sml: exact continuation rules.
- semantics/prop/vyperCallOutcomePropsScript.sml: checked traced equations.
- semantics/vyperCallOutcomeScript.sml: checked taking/adoption definitions.
- semantics/vyperStateScript.sml: storage_trace datatype and record operations.

## Notes

A separate read-only statement audit found the seven amended statements
provable under these exact definitions. The state/outcome/props theories have
already built; the frame theory's existing proofs have not yet been repaired.
Do not infer that an unbuilt statement is false from a failed tactic.
