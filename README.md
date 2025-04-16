# Vyper-HOL
Formal semantics for the [Vyper](https://vyperlang.org) programming language in the [HOL4](https://hol-theorem-prover.org) theorem prover.

## Status: Progress and Limitations

Currently, this repository includes a _formal_ and _executable_ definition of a subset of the semantics of Vyper, expressed as a _definitional interpreter_ in higher-order logic. The main function for executing Vyper statements is `eval_stmts` defined in `vyperInterpreterTheory` (`evaluate_def`).

The interpreter operates on abstract syntax (defined in `vyperAstTheory`) and produces effects on an abstract machine state (`abstract_machine`, defined in `vyperInterpreterTheory`) that represents the Ethereum virtual machine.

The following aspects of Vyper are currently not part of the formal model:
- concrete syntax, i.e. parsing
- type checking: the interpreter can fail during execution on badly-typed input, but we have not proved well-typed inputs don't fail
- external contract calls
- modules
- interfaces
- ABI encoding/decoding
- bounds checking and other checks for many of the types (e.g., the interpreter's `uint256` addition will currently overflow)
- several builtin functions are not yet included

## Repository Structure

The HOL4 script files that produce the formal theories are all in the root of the repository. We describe the main idea and contents of each theory as follows: TODO.

## Dependencies and Interactive Use

TODO: HOL and Verifereum dependencies and commits that are known to work
