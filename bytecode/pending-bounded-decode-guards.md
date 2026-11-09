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

The decoder-divergent fixtures are the ones listed in `decoder_divergent`.

## Stale oracles

`stale_oracle` lists fixtures whose pinned oracle lacks an upstream fix the HOL
compiler already follows. It is empty at the current pin, which already
contains vyper#5322, #5331 and #5332.
