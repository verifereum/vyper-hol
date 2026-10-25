# Membership element consistency (a10-09 / C2.1)

## Evidence and reproduction

Reviewed the operator-supplied G0003 artifacts in
`.agent-files/bytecode-validation/{report.json,execution-results.json,artifact-sha256.json}`.
The manifest identifies the individual source, exported AST, checked HOL input,
compilation equality, deployment/runtime bytecode, semantic equality, and runner
artifacts. `report.json` records reproduction commands and the full sources;
`execution-results.json` records each ABI signature, arguments, exact calldata,
initial storage, return/revert, EQ operands/memory and semantic-result reference.
These are externally executed finite experiments, not a new universal HOL theorem.

Vyper: 0.5.0a4, cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c,
experimental codegen, Prague, optimization NONE, no bytecode metadata.
HOL: `compile_vyper (K SOME) (o1_policy all_capabilities)` on inputs accepted
by both old checker modes. The artifact audit reports 24 kernel-derived
compilation equalities and 48 repaired `evaluate_membership` equalities, with
only DISK_THM tags and no cheat dependencies. Execution: py-evm 0.12.1b1
PragueVM, eth-abi 6.0.0, eth-utils 6.0.0, gas 1000000, value 0, empty storage.
Primitive-word and flag controls also have independent pinned-Vyper bytecode
comparisons and executions. No checker restriction was applied for these tests.

## Observed matrix

Each row has four runs: In and NotIn, each with matching and nonmatching values.
For a matching value source results are `(True, False)`; for a nonmatching value
source results are `(False, True)` (ordered In, NotIn).

| Element/path | Bytecode matching (In, NotIn) | Bytecode nonmatching (In, NotIn) | Conclusion |
|---|---|---|---|
| String[5], literal list | T, F | T, F | nonmatching false positive |
| Bytes[5], literal list | T, F | T, F | nonmatching false positive |
| one-field struct, literal list | T, F | T, F | nonmatching false positive |
| DynArray[uint256,2], literal list | T, F | T, F | nonmatching false positive |
| (uint256,uint256), literal list | T, F | T, F | nonmatching false positive |
| String[5], variable DynArray | revert, revert | revert, revert | successful source vs revert; cause not localized |
| Bytes[5], variable DynArray | revert, revert | revert, revert | successful source vs revert; cause not localized |
| DynArray[uint256,2], variable DynArray | revert, revert | revert, revert | successful source vs revert; cause not localized |
| one-field struct, variable DynArray | F, T | F, T | matching false negative |
| tuple, variable DynArray (HOL-constructed input) | F, T | F, T | matching false negative |
| uint256, literal list control | T, F | F, T | all agree |
| flag membership control | T, F | F, T | all agree |

Total: 48 runs; 26 disagreements, including 12 reverts; 22 agreements.
NotIn was executed independently, not merely inferred by complementation.

The task's `in_string_list`, `in_struct_dynarray`, and `in_nested_array` shapes
are represented by `string_in`, `struct_in`, and `nested_array_in` respectively
(and their NotIn counterparts). Additional literal/variable paths cover bytes
and tuples and controls. All aggregate literal-list representatives have an
actual non-reverting Boolean mismatch, so the domain conclusion does not rely
on the possibly unrelated variable-array decoding reverts.

## Aliasing and frontend boundary

Equal-content aggregate arguments are independently ABI-encoded at distinct
calldata locations. This does **not** imply that generated memory pointers are
distinct. For example `string_in_unequal` has x="ab", a="zz", offsets 68 and
132, and source False. Its bytecode returns True; both membership EQs at PCs
169/171 have operands (0,0), with the literal "b" in memory. Thus pointer
aliasing in generated code is observed, not assumed away. The analogous
literal-list controls must not be described as equal-content false negatives:
their demonstrated defect is an unequal-content false positive.

Pinned Vyper separately rejects all compiler-exported non-word membership
witnesses with TypeMismatch. Tuple variable-array syntax is rejected even
before AST export (StructureException: arrays of tuples not allowed). The
retained HOL tuple variable-array input substitutes TupleT[uint256,uint256]
into the exported nested-array program and reruns both checker modes; it is
not claimed to be an unmodified Vyper AST. Tuple literal-list inputs **are**
unmodified compiler exports and already exhibit the category's mismatch.

## Consequence for checker work

The observed partition is primitive-word/flag controls versus all five tested
aggregate classes (strings, bytes, structs, arrays, tuples). Each aggregate
class has a concrete Boolean mismatch, independently of real codegen rejection.
This supports C2.2's primitive-word element boundary; it is not a proof that
every aggregate subtype or every input disagrees, nor a universal correctness
claim for words. Preserve direct flag membership. No whitelist row is relaxed
by this diagnostic work, and no external #549/#560 residual is resolved here.

## Implemented checker boundary (C2.2)

`is_prim_word_type` in `vyperTypeSystem` now guards only the array disjunct
of `In`/`NotIn`. It includes uint, int, bool, address, decimal, fixed bytes
of at most 32 bytes, and flags, matching `compileEnv.is_word_type` exactly.
Direct flag membership is unchanged. No Eq/NotEq or whitelist rule changes.

`vyperMembershipSemanticsTestTheory` checks both operators at the
`well_typed_binop` boundary for arbitrary static/dynamic bounds: rejection
of strings, dynamic bytes, structs, tuples, nested arrays and oversized fixed
bytes; acceptance of all retained primitive classes and direct flags. Its
`membership_element_word_boundary` proves correspondence with lowering and
`membership_checker_lowering_boundary` exposes the typing consequence.
These are checker-rule tests. Final validation additionally checks the three
original aggregate witnesses with the strengthened checker in both modes;
see `membership-comparison-validation.md`. The external behavior experiment
above retains its original acceptance domain and is not rerun by that check.

The full `vyperTypeSoundnessTheory` and `vyperTypeBuiltinsTheory` rebuild
without proof changes: their existing proofs discard the strengthened premise.
`membershipCheckerIntegrityTheory` audits saved theorems in the type system,
builtin and expression soundness, soundness facade and membership tests,
rejecting assumptions, axioms and any oracle other than DISK_THM.
