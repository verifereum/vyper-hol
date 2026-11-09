# Fixtures out of parity: bounded memory ABI decoding and newer upstream fixes

The native runner expects the fixtures below to compile but to differ from the
pinned Python oracle (`decoder_divergent` and `stale_oracle` in
`native/compilerNativeParity.sml`). The runner fails if one of them starts to
match, so an entry is removed once its difference is gone.

## Bounded memory decoding

Decoding a bounded type from memory (external-call return data, `abi_decode`,
tuple and struct members read back from memory) differs from the pinned Python
in two ways:

- It reads the source at positions relative to the buffer base and checks each
  range, including the head word, before loading from it. The pinned compiler
  checks the payload end only after the load, and does not guard a wrapping
  `src + 32 + length` for bounded types.
- It copies a bytestring by its runtime length and zeroes the last data word
  first (vyper#5333). The pinned compiler copies the destination's maximum
  size.

The guards keep the decoder's proofs sound when the source buffer sits in the
spill region or is relocated, which a pointer-valued, load-first check does not.
Every decode of this kind is a few bytes longer in HOL, so each fixture whose
program decodes a memory value differs, including ones with no bytestring (for
example an external call with a `gas=` keyword). The oracles stay the pinned
compiler's output.

The decoder-divergent fixtures are the 30 listed in `decoder_divergent`.

## Stale oracles

The pinned compiler lacks upstream fixes that the HOL compiler already follows.
Their oracles come back into parity when the fix is added to `patches/` and the
oracle is regenerated. None of these three upstream changes applies to the pin
and the current series as is (their hunks touch code the pin does not have yet),
so each needs an adapted backport:

- `conversions/bys16_to_dec`, `conversions/bys32_to_i8` (vyper#5322)
- `internal-frames/p41_int_local_and_call`,
  `memory-stores/t01_tuple_assign_intcall`,
  `memory-stores/t06_tuple_assign_mixed_targets` (vyper#5331 and #5332)
