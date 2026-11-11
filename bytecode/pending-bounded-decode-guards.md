# Fixtures out of parity: bounded memory ABI decoding

The native runner expects the fixtures below to compile but to differ from the
pinned Python oracle (`decoder_divergent` in
`native/compilerNativeParity.sml`). The runner fails if one of them starts to
match, so an entry is removed once its difference is gone.

## What differs

Decoding a bounded type from memory (external-call return data, `abi_decode`,
tuple and struct members read back from memory) differs from the pinned Python
in two ways:

- It reads the source at positions relative to the buffer base and checks each
  range, including the head word, before loading from it. The pinned compiler
  loads the length or count word first and checks the payload end only after
  the load, and does not guard a wrapping `src + 32 + length` for bounded
  types.
- It copies a bytestring by its runtime length and zeroes the last data word
  first. The pinned compiler copies the destination's maximum size. This half
  is fixed upstream by vyperlang/vyper#5333 (`7d380818`).

Every decode of this kind is a few bytes longer in HOL, so each fixture whose
program decodes a memory value differs. Eight of the eleven fixtures decode
only static return types (`e19`, `e21`, `e22`, `e29`, `e30`, `e38`, `e45`,
`t04`); they differ only in addressing: the lowering reads at
`ADD [buf; 0]` and computes no `hi`, where the pinned compiler reads at the
buffer pointer directly. The other three (`e04`, `e05`, `e37`) decode a
bytestring and differ in the check order and the copy length too. The oracles
stay the pinned compiler's output.

## Why the HOL lowering checks before loading

The pinned order does not satisfy two facts the proof relies on:

1. No out-of-range decode succeeds. Venom's semantics charges no gas, and
   verifereum's gas and memory sizes are unbounded, so a load at
   `2^256 - 32` succeeds (given enough gas) and reads zero. The payload end
   `(2^256 - 32) + 32 + 0` wraps to `0 <= hi`, the copy reads zeros, and the
   decode returns an empty bytestring where the source semantics reverts.
   Excluding this case needs a bound on gas or memory that real executions
   satisfy.
2. Loads stay inside the source buffer. A small offset such as `0x100` into a
   96-byte buffer passes `actual_ptr >= parent` and loads at `buf + 0x100`
   before the payload-end check reverts. That load lies outside the buffer's
   allocation, possibly above the allocation frontier, which the memory
   invariants carried into Venom's memory-location concretization forbid
   (`inst_mem_below_frontier`). After code generation it can read a spilled
   word: if that word exceeds the bound while Venom reads zero, the two runs
   revert at different `ASSERT`s, and the step-by-step simulation breaks.

Matching the pinned compiler therefore needs both a real-execution gas or
memory bound for case 1, and memory invariants and a code-generation
simulation that allow an out-of-buffer load on a path that reverts before any
observable effect for case 2. Until then the guards stay, and the fixtures
listed in `decoder_divergent` are expected to differ.

## Two ways to remove the difference

Route A: the compiler checks before loading. The pinned decoder's bounded
memory path adopts the wrap-safe checks its `Bytes[INF]`/`DynArray[..., INF]`
path already uses:

- `clamp_bytestring`: `assert_abi_length_word_in_bounds` before loading the
  length, and `assert_abi_bytes_payload_in_bounds` after it;
- `clamp_dyn_array`: `assert_abi_length_word_in_bounds` before loading the
  count;
- `_decode_complex`: the static-footprint no-wrap check for every type, not
  only types containing an unbounded sequence.

On the pin, with the Venom pipeline, the 11 fixtures grow by 9 to 32 bytes
of runtime code at `-O1`, and by 3 to 28 bytes at the default optimization.
An external call returning `Bytes[64]` costs 6152 gas instead of 6068 (+84).
The HOL lowering checks positions relative to the buffer base rather than
absolute pointers, so the emitted code would still differ. Matching it also
needs one of two changes: the compiler emits relative positions, or the
lowering emits checked absolute pointers and the pointer-relocation proofs
(`access_ok`, `affine_pointer_ops`) admit their comparisons. The eight
static-type fixtures can match without either, by restoring direct pointer
addressing for static decodes.

Route B: the proof accepts the pinned order. Three changes are needed, two of
them to top-level statements:

- Memory invariants: `inst_mem_ok_in_fn` and `inst_mem_below_frontier`
  (`venom/compiler/unitTransformDefsScript.sml`), the pointer discipline
  (`fn_ptr_ok`, `access_ok` in `venom/compiler/ptrDisciplineScript.sml`) and
  the memory-location concretization simulation gain a case for a load
  outside its buffer whose block reverts whatever value the load returns.
  For a bounded length word at `src` with `src + 32 > hi` and no wrap,
  either `length > maxlen` or `src + 32 + length > hi` holds, so the block
  reverts.
- Code generation: `venom_asm_rel` lets the two runs revert at different
  `ASSERT`s of the same block when both revert with the same data.
- Wrapping offsets: the correctness theorems (`vyper_call_correct`,
  `e2e_deploy_correctness`) take a gas bound that real executions satisfy,
  for example `ctxt.msgParams.gasLimit < 2 ** 63` (EIP-1985) in
  `call_state_rel` and its deployment counterpart. Under it, a memory
  access past about `2^42` bytes runs out of gas, which
  `frame_resource_starved` already covers, and the stages carry "Venom
  touched memory past the bound" through to that outcome. The gas
  sufficiency theorems (`vyper_call_gas_sufficient`,
  `e2e_deploy_gas_sufficient`) need a matching change for return data with
  out-of-range head offsets: either their out-of-gas escape, today only a
  `RETURNDATACOPY`, also admits a decoder load, or `call_outcomes_ok`
  requires each callee's return data to have its ABI head offsets within
  the data.
