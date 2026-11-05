# Frozen external producer: exact case and missing fact

The frozen theorem has not been modified or proved. This report uses the TASK's
alternative of an exact case and missing fact. It is **not** a HOL theorem
instantiating the entire pass/trace antecedent.

## Checked case

`concretizeLayoutExternalOutcomeProbeTheory` builds without cheats. Its instruction
is `STATICCALL [Lit 7w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["result"]`.
The source is `init_venom_state "entry"`, with an empty outcome stream. The target
changes only `vs_outcomes`, supplying one failed outcome whose return data is
`[0w]`. Address 256 is outside the computed-precompile addresses.

* `external_probe_return_lengths`: both instructions return OK, but successor
  return-data lengths are 0 and 1 (closed semantic computation).
* `external_probe_no_observation`: for every D, these successors cannot satisfy
  `dead_result_rel D (Halt post) (Halt tpost)`.
* `external_probe_no_local_successor`: no possible OK target successor satisfies
  the demanded local relation, for ANY pointer relation, byte relation, demand,
  or variable mask. Determinism is used via equality of the OK results.
* `outcome_update_incoming`: replacing target outcomes preserves relocation_env,
  relocation_reader_context, and the complete incoming local_rel with the Halt
  observation, for arbitrary incoming states and masks.
* `external_probe_access_taint`: for arbitrary lo/G/fn/s, the instruction satisfies
  access_ok and entry-taint taint_ok. Both memory ranges have zero length.
* `external_probe_well_formed`: inst_wf, non-terminator, and not INVOKE.

## Audit of frozen antecedents

Lines refer to `concretizeLayoutLocalExternalScript.sml`.

* Lines 5-18: pass, context shape, fn_eom, distinct ids, initial-state checks,
  wf, memory invariant, allocation cache, pointer discipline, pointer validity,
  joint trace, selected configuration, resolved origins, lifetime, and function
  membership involve source-side objects only. None mention target `t`.
* Lines 19-26: all three incoming relations are invariant under the target-only
  update, by `outcome_update_incoming`.
* Lines 27-28: relocation_taint_le depends on demand/tn/un, not target state.
* Lines 29-31: the event, opcode membership, and execution equation constrain
  only the source. Thus **every frozen antecedent is invariant under replacing
  target vs_outcomes**, even when embedded in an otherwise valid source trace.

Source-side compatibility reasoning (not a fully instantiated HOL witness): use
one entry function, one block containing this instruction followed by STOP, no
allocations, no parameters, no invokes, and empty taints/provenance/origins. The
literal operands do not use pointers; checked access/taint obligations are
vacuous because memory lengths are zero. Static shape requirements do not ban
STATICCALL; the singleton output and six operands are checked well formed.
`joint_initial` sets the current block/index and uses entry_taint.
`joint_transition`'s next rule admits this non-terminating, non-INVOKE OK step
as `SOME (OriginOrdinary fuel post)` and advances to STOP.
`resolved_config_initial` supplies `[0]` and `[([],FEMPTY)]`; lifetime_ok at
initial depth zero accepts `[0]`. No source allocation relocation is needed.
A complete concrete context/pass/trace witness is not claimed here: the report
isolates the missing interface fact rather than evaluating a whole pipeline.

## Missing fact and its scope

Writing rq_s and rq_t for the requests consumed in the two runs, the mandatory
Halt observation already requires

```
LENGTH (FST (take_outcome rq_s s.vs_outcomes)).co_returnData =
LENGTH (FST (take_outcome rq_t t.vs_outcomes)).co_returnData
```

No incoming hypothesis constrains this. Current return-data length equality
says nothing about the next outcome's return-data length.

For the exhibited case (both consumed outcomes fail, zero return-copy size,
identical current state apart from outcomes, empty current request list), the
tight condition eliminating this particular obstruction is equality of the
consumed return-data lengths; with all return bytes dead, it suffices for the
successor Halt observation. With a general D one additionally needs equality
of non-dead returned bytes. The rest of the full local conclusion also requires
its pointer/byte and taint compatibility; no claim is made that length equality
alone proves the entire external-family theorem. Equality of streams is a
stronger candidate for oracle alignment, not a demonstrated sufficient repair
for CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 with relocated requests.

This case does not rely on `joint_read_exempt` or a revert-forward read. Adding
`~joint_read_exempt` would not address it. No premise was added and no frozen
file was edited. The existing target cheat remains; its requested proof build
criterion has therefore not been met.
