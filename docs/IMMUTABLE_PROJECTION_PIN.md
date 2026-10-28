# Immutable projection boundary (Vyper cd74ce4f)

Pin: `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`.

## Checked versus executable

Both backends' source checker accepts **constructor** projected immutable
assignment and nested pop after initialization. It rejects direct immutable
pop/append/augassign, and rejects projected mutations in runtime functions.
These are not a blanket root-inherited immutable prohibition.

Executed with pinned Python compiler + `eth-tester[py-evm]`:

| Constructor operation | Legacy | Venom experimental |
|---|---|---|
| `a[indices.pop()][0] = False` | executes, index once | same |
| `a[0] = [False]` | executes | same |
| `abi_encode(a[0], a[0].pop())` | executes | compiler panic |
| `abi_encode(a[indices.pop()].pop(), a[0])` | executes, index once | compiler panic |
| complex nested child pop | executes | compiler panic |

Assignments persist in deployed immutable data: runtime getter returns the
changed values. For `a = [[True,False]]`, legacy encodes the **old** `[True,False]`
first argument and `False` popped argument, then runtime reads `[[True]]`.
For `a = [[[True,False],[False,True]]]`, legacy encodes both old children and the
popped `[False,True]`; runtime reads only the remaining child.

Venom pop's exact failure is `CompilerPanic: Cannot load from location:
immutables`: `_lower_dynarray_pop` uses `builder.load`, not constructor-aware
`ctx.load_word`. Source-check success is **not** executable Venom agreement.
The HOL projected-pop behavior is validated against executable legacy semantics,
not invented as the meaning of the Venom compiler crash.

## Representation

`AbiImmutable token off tv` is a location in frame-wide `.abi_immutables`,
separate from local `.abi_memory` (keys include target address and source/id).
It preserves written cells beyond logical length: pop writes only length, so
its returned element pointer remains readable before unwrap. Constructor
assignment synchronizes live immutable locations using the operation footprint.

`unwrap_abi_operand` **always copies** immutable operands, including complex
ones, before lowering the next ABI argument, matching pinned
`context.unwrap/load_immutable_to_memory`. Local complex memory operands remain
aliases instead; their existing alias regressions are unchanged. ABI encoding
records both arena lengths and releases only newly allocated representation
suffixes on success and error. Older constructor backing remains live, including
writes; logical immutable mutations persist even when fresh representation
captures are released. This restores the exact incoming state for pure ABI
reads, without weakening source purity or dropping exceptional effects.
`initial_state` resets backing at a new evaluation frame; only logical immutable
values are serialized back to the abstract machine.

Pinned deployment initializes/reserves its immutable section before constructor
execution (`codegen/module.py` and `codegen_venom/module.py`); the HOL arena starts
from initialized immutable values and zero-filled unused capacity. Runtime
immutable reads use copies from deployed data; runtime source mutations never
reach the evaluator through the checked boundary.

Reproduction artifacts: `.agent-files/immutable-projection-effects-pin.py` and
`.agent-files/immutable-projection-execute-pin.py`, with corresponding `.log`
files. Run with `PYTHONPATH=.agent-files/folded-value-validation/vyper-src`,
`SETUPTOOLS_SCM_PRETEND_VERSION_FOR_VYPER=0.5.0a4+cd74ce4f`, and
`.agent-files/folded-value-validation/venv/bin/python`.

Kernel regression target: `vyperAbiImmutableProjectionTestTheory` (eight proved
regressions). Targeted builds passed without CHEAT: State, AbiOperand,
Interpreter, AbiMemoryProps, unchanged AbiAliasTest, and the new projection test.
Additional exact-byte constructor-assignment reproduction:
`.agent-files/immutable-smallstep-pin.py` / `.log` executes both backends,
asserting ABI words `[32,2,0,0]`, exhausted index array, and persistent
`[[False,False]]` immutable data. CPS regressions are in
`vyperAbiImmutableSmallStepTestTheory`, including exact-state pure-read cleanup
and exceptional cleanup retaining logical immutable mutation.

Broader ABI typing/frame consumers must account for the new immutable arena:
relations allowing only `.abi_memory` changes need the corresponding
`.abi_immutables` frame premise, and operand typing needs `AbiImmutable` coverage.
An attempted broader SmallStep build stopped in its concurrently edited
`eval_expr_cps_def` termination proof, not in these target theories.
