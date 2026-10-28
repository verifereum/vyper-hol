# Shared ABI encoder proofs

The source-value and descriptor/window encoder contracts now derive from one
recursive execution proof. Both existing recursive APIs retain their statements;
`compile_abi_encode_to_buf_frag` supplies the source-value contract consumed by
external returns. No compiler implementation or source-language restriction is
introduced by this refactor.

## Contracts

All three interfaces describe `compile_abi_encode_to_buf` from
[abiEncoder](defs/abiEncoderScript.sml). Their differences concern inputs and
memory guarantees, not alternative compiler implementations.

| Interface | Input | Result and memory guarantee |
| --- | --- | --- |
| `abi_encoder_correct` | Typed ABI descriptor/value windows, disjoint numerical reserve, fresh generated variables, allocator budget and exit-PHI condition | Encoded bytes, length, decoder effect and continuation simulation |
| `abi_scratch_encoder` | The same typed windows, with separation from the physical scratch footprint including registered allocations | Encoded bytes, length, precise scratch evolution and continuation simulation |
| `compile_abi_encode_to_buf_frag` | A semantic `abi_enc_plan`, typed source value and memory, evaluated operands, and the existing `enc_pre` | Source ABI bytes and length, the exact `enc_frame`, and `frag_exec` |

The first two contracts alone were insufficient for the third. Their aggregate
ABI typing imposes cardinality bounds that do not follow from every source
value. Also, framing the physical scratch reserve does not by itself frame every
registered allocation. The source contract permits stale generated-variable
bindings, whereas the recursive runners require fresh bindings.

## Shared execution

[abiEncoderSharedContract](abiEncoderSharedContractScript.sml) introduces the
shared input and endpoint contracts. Aggregate source windows use
`abi_encoder_open_input`: leaves retain their typing requirements, while
aggregate composition does not add a global ABI cardinality bound. Dynamic
arrays retain their existing representable runtime-length requirement.

The endpoint records bytes, length, physical scratch effects, registered memory
effects, conditional preservation of allocation validity, control position and
execution simulation at the **same state**. The simulation also supports adding
back pre-existing variable bindings. This prevents separate executions from
being used to establish incompatible parts of the postcondition.

The factored sequence, member and array engines establish those observations
for the actual generated instructions. Static and dynamic members use the
shared member engine; arrays use the existing finite-iteration infrastructure.
Empty arrays, zero-size elements and omitted fixed-array defaults remain
covered. Parent cursor allocations remain in the enclosing ownership ledger
even when they precede a child's instruction interval.

[abiEncoderSharedRecursive](abiEncoderSharedRecursiveScript.sml) contains the
single admissibility induction. The six existing exports in
[abiEncoderCorrectRecursive](abiEncoderCorrectRecursiveScript.sml) and
[abiScratchEncoderRecursive](abiScratchEncoderRecursiveScript.sml) are projection
wrappers with unchanged statements and attributes.

## Source and return adapters

The dependency order is:

1. Source-memory windows and encoding-equivalent representatives in
   `abiEncoderSourceWindow`, `abiEncoderSourceAggregate`,
   `abiEncoderSourcePrimitive` and `abiEncoderSourceProducer`.
2. Shared leaf, member and array execution, then the shared recursive closure.
3. `abiEncoderEntry`, `abiEncoderResourceAdapter` and `abiEncoderSourceInvoke`
   derive freshness, budgets, separation, exit-PHI facts and invocation from
   the original source premises.
4. `abiEncoderVarRestore` restores original variable bindings while preserving
   generated outputs and every required non-variable state field.
5. `abiEncoderFragmentFrame` recovers the exact existing frame;
   `abiEncoderFragment` packages the original source-value theorem.
6. `loweringHalt` consumes that standalone theorem for ABI returns.

Static copies use an encoding-equivalent representative when the original ABI
aggregate fails the descriptor interface's typing bound. This is equality of
encoded bytes, not a new assumption about the source type. In particular,
arbitrarily large collections of zero-size static components do not acquire a
new cardinality restriction. Zero-size and sparse-default witnesses remain.

Superseded intermediate source/scratch interpretations, restrictive bytes and
string adapters, an alternate static representative chain, and an unused
instruction-specialization helper were removed. Their consumed shared transport
facts and the separate witness, observer and audit evidence remain.

## Relationship to the earlier PRs

- [#682](https://github.com/verifereum/vyper-hol/pull/682) supplies useful
  static-copy and framing groundwork. Retain the corresponding existing
  memory/copy lemmas instead of importing another parallel encoder proof.
- [#728](https://github.com/verifereum/vyper-hol/pull/728) supplies source-level
  contracts, prefix algebra and the external-return consumer. Its older
  dynamic-loop helper takes a payload-base destination; the current helper
  takes the array base and adds 32 internally. Effective payload addresses
  agree under that change of convention, but emitted instruction sequences
  differ, so old loop execution proofs cannot be reused verbatim.
- [#762](https://github.com/verifereum/vyper-hol/pull/762) supplies the current
  compiler behavior and recursive window framework. Retain its decoder bounds,
  recursively clamp-free bulk decoding, tuple staging, tuple wrapping,
  flags256 and empty-allocation provenance fixes and their compiler fixtures.
  Canonical encoder proofs and noncanonical decoder acceptance proofs establish
  different properties; neither substitutes for the other.

The legacy mutual `compile_abi_encode_frag` remains admitted and retains its
original statement. Its dynamic-loop clause describes the old payload-base
convention and is not a claim about the current helper. The standalone
source-value theorem and its return consumers do not use that admission.
Retiring or restating the remaining legacy clauses is a separate API decision;
no hypothesis has been strengthened to preserve them here.

Removal of proof-audit tooling and unrelated integrity checks is outside ABI
consolidation. This refactor retains the audits and does not include those
removals.

## Validation and review surface

[abiEncoderReuseAudit](abiEncoderReuseAuditScript.sml) is a build root. It checks
propagated admission tags and undischarged hypotheses for the shared closure,
source bridge and ABI-return consumers, together with the retained boundary
witnesses and observer evidence. Only `DISK_THM` tags are accepted.
Loaded HOL theory files do not preserve upstream axiom dependencies, so the
current-session axiom check is not a transitive upstream axiom-freedom claim.

The dedicated `evalCompilerAbiTupleString` fixture is a build root. Its source,
AST and bytecode remain in the dedicated ABI corpus. The base branch already
removed the unmanifested copy in the primary oracle source directory.

[The contract index](ABI_ENCODER_REUSE_API.md) flags every new definition,
inductive relation and theorem statement. Existing declarations are unchanged;
there are no new axioms or admissions. Validation builds the touched theories
and their necessary dependencies. The full CI matrix and opt-in bytecode parity
rollup are not local validation targets.
