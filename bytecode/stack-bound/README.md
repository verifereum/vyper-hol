# Operand-stack checker

`bytecode_stack_check fuel limit code` explores runtime bytecode from pc 0
with an empty stack. Abstract stack words retain constants through PUSH,
DUP and SWAP. An unknown jump explores every valid JUMPDEST. The checker
rejects if it exhausts fuel or reaches a stack longer than `limit`.

`stackBoundSoundnessTheory.bytecode_stack_check_no_overflow` proves that
a passing check with `limit <= stack_limit` excludes `frame_raises es
StackOverflow` for a well-formed frame entering that bytecode with pc 0,
an empty stack and no pending jump. `bytecode_stack_check_step_no_overflow`
gives the corresponding result for `step` at an instruction reached in
that frame. CALL/CREATE continuations include their eventual result word;
external callees require their own checks. The result concerns operand-stack
overflow and does not exclude other execution failures.

`stackBoundWitnessesTheory` checks existing compiled internal-call bytecode
and the deep-chain fixture here.

`deep_chain.vy` has 120 internal functions, each with eight `uint256` arguments.
Each caller uses all eight arguments after its internal call, keeping them
live across the call. The fixture is compiled with stock Vyper at `VYPER_PIN`,
experimental code generation, `-O1`, Prague, and no bytecode metadata.
`provenance.json` records the compiler and source hash.

With that compiler installed and `PYTHONHASHSEED=0`, regenerate from the repo
root with:

```sh
vyper --experimental-codegen --evm-version prague -O1 \
  --disable-bytecode-metadata -f bytecode,bytecode_runtime \
  bytecode/stack-bound/deep_chain.vy
```

The two output lines are the `deploy` and `runtime` fields of `deep_chain.hex`.
The witness theory checks rejection at 1024 and acceptance at 2048 with the
same fuel. The larger limit is a checker parameter, not an EVM execution limit.
