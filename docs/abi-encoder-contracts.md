# ABI encoder contracts

The ABI encoder has three interfaces because callers describe source memory
and scratch ownership differently. Each describes execution of the same
`compile_abi_encode_to_buf` compiler definition, not a separate encoder.

## Interfaces

| Contract | Inputs | Guarantees |
| --- | --- | --- |
| `abi_encoder_correct` | A typed ABI descriptor/value window, nonwrapping source and output regions, separation from a numerical scratch reserve, fresh generated variables and an allocator budget | Encoded bytes and their length, the numerical-reserve memory effect, and continuation simulation |
| `abi_scratch_encoder` | Typed descriptor/value windows separated from the physical scratch footprint, including registered allocations, with the same freshness and budget conditions | Encoded bytes and their length, physical scratch evolution and its memory frame, and continuation simulation |
| `compile_abi_encode_to_buf_frag` | A semantic `abi_enc_plan`, a typed source-language value in memory, evaluated source/destination operands, and `enc_pre` | Source-language ABI bytes and their length, exactly `enc_frame`, and `frag_exec` |

The descriptor contracts also require emitted code to be present in the
containing function and a compatible exit PHI prefix. The source fragment
derives its execution conditions from its existing premises. It permits stale
bindings for generated variables; freshness is not an extra caller assumption.

## Shared execution

`abi_encoder_shared` proves one execution with a single endpoint containing
the encoded bytes, result length, scratch effects, registered-allocation frame,
conditional preservation of allocation validity, and continuation simulation.
Keeping these observations at the same endpoint lets callers combine them.
The leaf, member and array proofs feed one structural admissibility induction.
`abi_encoder_correct_admissible` and `abi_scratch_encoder_admissible` project
their respective contracts from that shared result; their translation
corollaries cover descriptors produced by `type_to_abi_enc_info`.

The shared input predicate, `abi_encoder_open_input`, retains leaf typing
while allowing aggregate composition without imposing a global ABI cardinality
bound. Dynamic arrays retain their representable runtime-length requirement.
This matters for source values with many zero-size components: a source-value
proof must not acquire a descriptor typing bound that its caller never assumed.

## Source values and returns

The source adapter constructs a window with the same encoding as the source
value, invokes the shared execution, restores prior variable bindings, and
recovers `enc_frame`. An encoding-equivalent representative supports static
copies without strengthening the source type's assumptions. The resulting
`compile_abi_encode_to_buf_frag` is consumed by the ABI-return proofs in
`loweringHalt`.

The source contract's frame preserves existing registered allocations outside
the declared output; a numerical scratch-reserve frame alone does not imply
that guarantee. The shared endpoint therefore retains both physical scratch
effects and registered-allocation effects.

## Compiler fixtures

The `abi-codegen` corpus contains twelve pinned-Python source, AST and bytecode
fixtures. Its provenance is reproduced by
`lowering/defs/bytecode/python-o1-bytecode-fixtures --check --vyper-repo PATH`.
The ABI parity theories compare compiler output with those bytecode fixtures;
this is finite differential evidence, not a universal compiler equivalence
theorem. See [compiler-definition-parity.md](compiler-definition-parity.md) for
the repository pin and compiler boundary.
