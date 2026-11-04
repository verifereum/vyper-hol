# External outcome interface checkpoint (C2.4.26.7)

## Actual semantic updates

- CALL / STATICCALL (`venomExecSemantics`, exec_ext_call): common
  `venom_call_request` plus common outcome queue determines common output,
  adopted accounts/transient/logs/deletions, returndata, remaining outcomes,
  and recorded requests. `consume_call_outcome` writes exactly
  `TAKE retSize outcome.co_returnData`, not padded bytes. Output is then
  bound by `update_var`.
- DELEGATECALL (`exec_delegatecall`, `extract_venom_result`): common EVM
  initial state gives common `run` result without unfolding `run`. Success
  takes accounts/transient/deletions and logs from that result; failure
  keeps the original accounts/transient/deletions and appends no logs.
  Both update returndata and write `TAKE retSize returndata`. The outcome
  queue and requests are unchanged. Then the common output variable is bound.
- CREATE / CREATE2 (`exec_create`, `consume_create_outcome`): common request
  and queue determine common adoption of accounts/transient/logs/deletions,
  returndata, remaining outcomes and requests. There is no return-memory
  write. Oversize initcode aborts via `halt_state (set_returndata [] s)`;
  terminal coarse congruence is separate from continuing local simulation.

All these record updates leave allocation maps, variables (before the final
output binding), cursor, FMP and other operational fields unchanged.

## Checked post-outcome boundary

`deadStoreElimExternalUpdates` defines a common seven-field update
`dse_external_update accounts ts logs dels rd os rqs s`, proves Memory
local agreement is preserved under common values, and exports the unchanged
allocation-map projection. DELEGATECALL supplies the already-equal old
outcomes/requests; failure branches supply already-equal original account
and transient fields. Consumers can rewrite their reconstruction once into
this update instead of unfolding local agreement again.

## Existing actual-write boundary (do not duplicate)

`dse_local_agrees_memory_overwrite` in `deadStoreElimStoreSteps` states:

```
dse_local_agrees AddrSp_Memory P s t ==>
dse_local_agrees AddrSp_Memory
  (FILTER (\(loc,(b,n)). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
  (write_memory_with_expansion a bytes s)
  (write_memory_with_expansion a bytes t)
```

Use `bytes = TAKE retSize rd`. Its length is `MIN retSize (LENGTH rd)`
(`LENGTH_TAKE`), including zero on an empty return. Outcome updates commute
with memory writing: their definitions touch disjoint fields. Common output
binding uses `dse_local_agrees_update_var` afterward.

## Proposed next consumer contract

For a retained Memory CALL/STATICCALL/DELEGATECALL with source OK, original
pending-at, local agreement and instruction lookup, establish equal input
bytes using the precise read footprint, then equal request or EVM input.
Obtain equal result bytes and outcome fields. Return matching target OK
with local agreement on the above actual-length filtered P, and pending-at
at SUC cursor on that same list. Transport pending runtime witnesses using
the unchanged alloca map. CREATE has the same contract with unfiltered P.
Non-OK outcomes use existing terminal boundaries rather than weakening the
OK relation.

Pending suffix advancement must prove the instruction cannot fully clobber
any surviving witness. It must not infer a full clobber from the declared
maximum output size: basePtrDefs.bp_segment_from_ops uses iao_size, and
CALL-family write locations have no exact size (basePtrDefs lines 293-296).
Thus their static footprint is not fixed. Inspect and prove this no-clobber
fact before external semantic integration; it is not assumed by the checked
common-outcome preservation lemma.
