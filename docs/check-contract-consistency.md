# Checker-domain consistency probes

[Issue #571](https://github.com/verifereum/vyper-hol/issues/571) requires behavioral
checks before rejecting declared types or statement forms merely because Vyper
rejects their source syntax. The probes below found no additional restriction to
introduce for the accepted cases they exercised. These are finite observations,
not universal compiler-correctness theorems.

The checked source revision was `d255fdd77baa2cd07d60782968bfb76000245900`.
Accepted sibling programs were exported using Vyper
`9362e36b145c4b63ceb6a893018ea970e78bf6a6`, with optimization `NONE`, experimental
code generation, Prague, and no bytecode metadata. Each mutated HOL program was
checked for runtime and deployment, compiled with
`compile_vyper (K SOME) (o1_policy all_capabilities)`, and evaluated with
`call_external`. The resulting HOL runtime bytes were executed independently with
py-evm `0.12.1b1`'s Prague VM. Python-Vyper bytecode was not substituted for them.

## Declared types

The basic accepted sibling was a pure external identity function, `f(x: T) -> T`.
Its declaration and expression type annotations were mutated together. Named
types also retained their declarations, with fields or flag members changed for
the empty cases. Fifteen projections from freshly exported sibling ASTs were
checked to equal the exact HOL ASTs used for the computations.

Both checker modes gave the same decision in every row.

| Type or mutation | Checker | Inputs and observed behavior |
|---|---|---|
| `uint8` to `uint7` | Reject | Already outside the checker domain. |
| `int16` to `int12` | Reject | Already outside the checker domain. |
| `uint0`, `uint264`, `bytes33` | Reject | Invalid-width controls. |
| `bytes4` to `bytes0` | Accept | Empty value returned one zero ABI word; a nonempty value errored in the source and reverted in the EVM. |
| `String[7]` to `String[0]` | Accept | Empty string returned normally; `"a"` errored in the source and reverted in the EVM. |
| `Bytes[7]` to `Bytes[0]` | Accept | Empty bytes returned normally; one byte errored in the source and reverted in the EVM. |
| `DynArray[uint256, 7]` to bound zero | Reject | Both dynamic and fixed zero bounds are already excluded. |
| Dynamic to fixed array of `String[5]`, length two | Accept | `["a", "bc"]` returned with matching ABI bytes. |
| Dynamic to fixed array of `Bytes[5]`, length two | Accept | `[0x01, 0x0203]` returned with matching ABI bytes. |
| Dynamic to fixed array of a two-member flag, length two | Accept | Flag values `[1, 2]` returned with matching ABI words. |
| Array of `(uint256, bool)` tuples, dynamic bound two | Accept | `[(7, True), (9, False)]` returned with matching ABI bytes. |
| Empty tuple parameter | Reject | Already excluded by `assignable_type`. |
| Empty struct parameter | Reject | Already excluded by `assignable_type`. |
| Flag with no members | Accept | Value zero returned normally, with matching ABI word zero. |

Unmodified `uint8`, `int16`, `bytes4`, `String[7]`, `Bytes[7]`, and dynamic-array
siblings provided accepted controls. Integer inputs included zero, positive and
negative boundary values, and out-of-range values. Rejected types were not used
to infer a defect inside the current checker's domain. In particular,
`evaluate_type` already checks byte-aligned integer widths and positive array
bounds at this revision.

For the dynamic byte, string, and tuple-array results, the external argument and
return each used the ordinary single-value ABI tuple wrapper. The calls used
empty storage and performed no storage, log, or external-call operations.

## Storage reads and writes

The storage probes used revision `da829c33a2956dfd0c35612caf20b49654c02f6d`
and the same pinned export and execution settings. Each fresh accepted sibling
declared an untouched `uint256` guard at slot 0 and a cell at slot 1. Its external
`f(x: T) -> T` assigned `self.cell = x` and returned `self.cell`; a separate view
function `g() -> T` read the existing cell. Type mutations replaced the whole
cell/argument/result type throughout the translated modules. The tuple-array
sibling used `DynArray[uint256, 2]` before that substitution. The layouts had no
declarations after the cell, so the larger tuple elements did not overlap another
variable.

Both checker modes accepted all eleven programs below. Each was run with all-zero
storage and with the populated cell shown below plus guard slot 0 set to 99 and
untouched slot 12 set to 77. Zero-width cells retained their valid empty value in
that second state. Both `g()` and `f(x)` started independently from each initial
state, giving four calls per program.

| Cell type | Populated cell | Value written by `f` |
|---|---|---|
| `bytes4` | `0x61626364` | `0x65666768` |
| `bytes0` | empty bytes | empty bytes |
| `String[7]` | `"hi"` | `"bye"` |
| `String[0]` | empty string | empty string |
| `Bytes[7]` | `0x6869` | `0x627965` |
| `Bytes[0]` | empty bytes | empty bytes |
| Fixed array of two `String[5]` | `["a", "bc"]` | `["d", "ef"]` |
| Fixed array of two `Bytes[5]` | `[0x61, 0x6263]` | `[0x64, 0x6566]` |
| Fixed array of two flags | `[1, 2]` | `[2, 1]` |
| Dynamic array of two `(uint256, bool)` tuples | `[(7, True), (9, False)]` | `[(11, False), (13, True)]` |
| Flag with no members | 0 | 0 |

All 44 calls matched both the returned ABI bytes and final storage at every slot
from 0 through 12. The source return values came from `call_external` and were
encoded with `evaluate_abi_encode_bytes`; final slots came from its returned
machine's account storage. The independent EVM runs used the emitted HOL runtime
and the identical initial slot words. The guard values remained unchanged.
These finite storage observations found no additional declared-type restriction.

## Empty ranges and argument writes

The range siblings initialized `t = 5`, added the loop index in the body, and
returned `t`. Replacing the finish literal of `range(1)` by zero, or that of
`range(3, 4)` by three, retained the translated loop bound of the accepted sibling.

The write siblings first copied argument `x` into local `y`, modified `y`, and
returned it. The mutations redirected the assignment target and subsequent reads
from `y` to `x`, retaining the local declaration. The array case used a fixed
three-element `uint256` array.

| Program | Runtime/deploy checker | Source result | EVM result |
|---|---|---|---|
| `range(1)` sibling | Accept/accept | 5 | ABI word 5 |
| Mutated `range(0)` | Accept/accept | 5 | ABI word 5 |
| `range(3, 4)` sibling | Accept/accept | 8 | ABI word 8 |
| Mutated `range(3, 3)` | Accept/accept | 5 | ABI word 5 |
| Local word write, argument 41 | Accept/accept | 42 | ABI word 42 |
| Redirected argument word write, argument 41 | Accept/accept | 42 | ABI word 42 |
| Local array write, argument `[1, 2, 3]` | Accept/accept | 5 | ABI word 5 |
| Redirected argument array-element write, argument `[1, 2, 3]` | Accept/accept | 5 | ABI word 5 |

These observations provide no mismatch requiring an additional empty-range or
argument-write rule under issue #571's consistency policy. They describe the
checked revision; independently requested changes to argument assignability are
separate from this result.

## Validation and limits

The HOL computations were built as `issue571ControlTheory`,
`issue571WordsTheory`, `issue571CompositesTheory`, `issue571ProjectionTheory`, and
`issue571StatementsTheory`. The latter two checked the fresh-AST projections and
the source-fronted statement mutations. All computations completed, and each
accepted source success listed above matched the independent EVM return bytes;
the listed source errors matched EVM exceptions.

The checks cover these concrete programs and inputs. They do not establish
universal consistency, exercise every declaration position, or prove the full
`call_result_rel` relation for arbitrary initial states. They do not replace
the separate builtin-argument fixes, buffer-sizing work, soundness proofs, or
compiler fixture checks required by issue #571.

## Widened builtin annotations

Fresh exports at the same Vyper pin confirm that a wider expected type changes
the builtin Call node's own annotation, not just its return or assignment target.
Each program retains a runtime parameter.

| Expression and context | Call node bound | Operand capacities |
|---|---:|---|
| `return concat(X, y, b"xyz")` into `Bytes[100]`, with constant `X: Bytes[10]` and parameter `y: Bytes[5]` | 100 | 10 + 5 + 3 |
| `c: Bytes[60] = concat(y, b"x")`, with parameter `y: Bytes[50]` | 60 | 50 + 1 |
| `a: Bytes[100] = slice(y, 0, 2)`, with parameter `y: Bytes[50]` | 100 | source 50, literal length 2 |
| `b: Bytes[100] = slice(y, i, i)`, with parameters `y: Bytes[50]`, `i: uint256` | 100 | source 50 |
| `return slice(a.code, 0, 2)` into `Bytes[100]`, with parameter `a: address` | 100 | code source, literal length 2 |

All five compile. A checker requiring equality between the result annotation
and inferred payload capacity would reject these valid programs. The frontend
reads the Call annotation directly. Capacity inequalities preserve these
programs while excluding the undersized buffers described in issue #571. These
exports establish the producer domain; they do not by themselves establish
bytecode parity or compiler correctness for the changed lowering.

### Bytecode comparisons

The wider local case crosses an allocation-word boundary and exposes a baseline
parity failure. These comparisons use the same compiler settings as the exports
above, including disabled metadata.

| Program | HOL/Python runtime bytes | Exact bytecode match | Execution with `y = b"ab"` |
|---|---:|---|---|
| `c: Bytes[60] = concat(y, b"x")`, `y: Bytes[50]` | 400/400 | Yes | Both return `b"abx"`. |
| `c: Bytes[100] = concat(y, b"x")`, `y: Bytes[50]` | 400/401 | No; first differing byte at zero-based offset 54 | Both return `b"abx"`. |
| `return concat(y, b"xyz")` into `Bytes[100]`, `y: Bytes[5]` | 341/341 | Yes | Both return `b"abxyz"`. |

The differing local case has deployment lengths 421/422 bytes. The sampled EVM
returns agree, so this is evidence of bytecode divergence rather than a source
semantics counterexample. It supplies a regression for issue #571's Concat
buffer-sizing repair.

The retained `evalCompilerConcatWidenedTheory` regression checks the corrected
lowering against that same independent Python oracle. With a 51-byte temporary
capacity, `lowered_value_type` also describes 51 bytes so assignment staging
uses the produced type. The returned value tag retains the expression's
annotation, as for byte literals and ABI encoding. Exact deployment and runtime
equality now passes: 422 and 401 bytes respectively. The frontend checks both
deployment and runtime acceptance before this comparison. This is finite parity
evidence for the repair, rather than a general simulation theorem.

Fixed-byte arguments need additional physical space because an unaligned
`MSTORE` writes a full word. The allocation also covers the furthest such store,
following [vyperlang/vyper#5295](https://github.com/vyperlang/vyper/pull/5295).
For `Bytes[10]` followed by `bytes4`, that changes the buffer request from 64 to
74 bytes without changing the logical 14-byte bound. Applying that exact
upstream lowering fix to the pinned compiler preserved all fifteen existing
Concat deployment/runtime oracles; this fixture remains 332/311 bytes.
`concat_fixed_word_allocation` checks the 65-byte request for two `bytes1`
operands and the 74-byte request for the mixed case.

The three widened Slice witnesses also pass both checker modes. Their deployment
and runtime bytes match Python exactly on the checked baseline:

| Expression | Deployment/runtime bytes, identical on both sides |
|---|---:|
| `slice(y, 0, 2)` into `Bytes[100]`, `y: Bytes[50]` | 351/330 |
| `slice(y, i, i)` into `Bytes[100]`, `y: Bytes[50]` | 371/350 |
| `slice(a.code, 0, 2)` into `Bytes[100]` | 283/262 |

These comparisons establish the expected acceptance and parity controls before
the stricter undersized-bound checks are introduced. They do not prove the
separate Slice simulation theorem.

The constant-prefixed `concat(X, y, b"xyz")` export compiles with Python and
passes both HOL checker modes, but baseline `compile_vyper` returns `NONE`.
Its projected HOL expression retains a `TopLevelName` for `X`. This is covered by
the constant-substitution work in [issue #565](https://github.com/verifereum/vyper-hol/issues/565);
that prerequisite must be consumed before this witness can check Concat parity.
