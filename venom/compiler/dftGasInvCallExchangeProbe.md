# Returning-call exchange interface audit

## Checked computation

`dftGasInvCallExchangeProbeTheory` checks a concrete INVOKE of a single-block
callee returning `[42w]`, independent ADD of `2w + 3w` to `v`, and call output
`r`. It checks `dft_gas_swap_pair`, both inst_wf facts, all four actual indexed
steps, and equality after normalizing the final index to 2. The same constant
oracle `7w`, frame `[]`, depth 0, fuel 1 and context are used in both orders.
This is a successful returning run, not an assumption that a modified call
terminates. It is a bounded example, not a general exchange theorem; it does
not exercise a GAS inside the callee or prove any function-shape envelope.

## Field audit (venomExecSemantics definitions)

`setup_callee` fails only on an empty block list. Otherwise it overwrites:

* vs_vars with FEMPTY; vs_params with evaluated args;
* vs_current_bb with entry label; vs_inst_idx with 0; vs_prev_bb with NONE;
* vs_halted with F; vs_allocas with FEMPTY;
* vs_fmp and vs_call_entry_fmp with caller vs_fmp;
* vs_return_pc_token with last argument, or 0 for no arguments.

Every other state field is inherited unchanged, notably vs_alloca_next,
vs_initial_fmp, memory, transient state, accounts, returndata, logs, outcomes,
requests, pending deletions, gas readings, immutables, labels, code, data section,
call/transaction/block contexts and previous hashes. A caller variable update
and index change are erased here. They must NOT be confused with a change to
FMP, memory, gas readings, or another inherited field.

`merge_callee_state` overwrites exactly memory, transient, accounts, returndata,
logs, outcomes, requests, pending deletions, gas readings and immutables from
the callee. All other fields remain those of the original caller, including
vars, params, control flow, contexts, allocations, alloca_next, initial FMP,
call-entry FMP, return token, code/data/labels/previous hashes, and caller FMP.
`adopt_return_fmp` subsequently changes just vs_fmp if iret_adopt_fmp is SOME.
`bind_outputs` checks arity then updates caller variables. Thus a disjoint
caller variable update commutes through merge/adopt/bind; it is not imported
from callee variables.

## Premises at the intended swap-pair consumer

INVOKE reads and writes `all_effects`. `effects_independent` in
`dft_gas_swap_pair` consequently forces the partner's tracked read/write effects
to be empty. In particular memory, transient/storage/account effects and FMP
operations cannot cross. ALLOCA, terminators and pseudo instructions are
independently excluded by the swap-pair clauses. Two INVOKEs cannot be such a
pair. The empty-effect condition is not by itself a proved variable-update
semantic classification: this still needs opcode/semantic validation, including
metadata/context reads and potentially failing pure instructions.

The two def/use disjointness clauses prevent the partner's output variables
from being call arguments and the call's outputs from being partner inputs;
the def/def clause prevents output overwrites. For a variable-only partner,
argument evaluation is therefore unchanged. The caller fields which such a
partner may read apart from variables must also be shown unchanged by the
successful call. GAS is special only as an oracle event: ev_gas changes a
variable and does not consume vs_gas_readings. The fixed event key (p,d,id) does
not depend on the instruction index or on the callee's execution order.

## General boundary still needed (not asserted as a theorem here)

For unchanged args, function and shared inherited fields, the key initialization
identity is:

```
setup_callee fn args (update_var out value s with vs_inst_idx := n)
  = setup_callee fn args s
```

It follows directly from the overwritten-field list, not from any assumption
that two independently run callees terminate. Once this identity and argument
framing are proved at the actual consumer, the SAME finite `ev_blocks` witness
can be reused by congruence, with the identical oracle frame `(d,id)::p`, depth,
fuel and context. No recursive frame-replay induction is needed for this
variable/index-only difference. If a proposed partner changes inherited fields,
this identity does not apply and a stronger replay relation would need proof.

The connected general call-frame boundary should yield, for a variable `out`
absent from INVOKE args and outputs, equality of OK results under update_var,
and preservation of non-OK results as appropriate (compare the existing
`step_inst_invoke_frame` interface, but do not silently replace ev_blocks by
run_blocks). The semantic producer for an arbitrary allowed pure partner and
the reverse-order success argument must be supplied, not postulated as another
conditional exchange premise. Index normalization follows the existing kernel
pattern, with caller index retained on successful returns.

## Planning consequence

The concrete probe supports returning-call exchange for the chosen pure pair.
The source field audit suggests exact callee-input equality, rather than a
large recursive replay invariant, for variable/index-only partner changes.
Request a connected general call-frame/classification/kernel plan. Cross-context
finite-return reflection is DIFFERENT: changed contexts do not permit reuse by
input equality and still require the fuel-induction argument. Nothing here
proves source-prefix extraction or the frozen lowered-memory theorem.
