# Vyper-HOL
Formal semantics for the [Vyper](https://vyperlang.org) programming language in the [HOL4](https://hol-theorem-prover.org) theorem prover.

## Status: Progress and Limitations

Currently, this repository includes a _formal_ and _executable_ definition of a subset of the semantics of Vyper, expressed as a _definitional interpreter_ in higher-order logic. The main function for executing Vyper statements is `eval_stmts` defined in `vyperInterpreterTheory` (`evaluate_def`). Top-level entry points are `load_contract` and `call_external`, defined in the same theory. Examples of calling these functions and executing the interpreter can be found in `vyperTestScript.sml`.

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

## Dependencies

This work is developed in the [HOL4 theorem prover](https://hol-theorem-prover.org), and makes use of the Ethereum Virtual Machine (EVM) formalisation in the [Verifereum](https://verifereum.org) project. The [Verifereum repository](https://github.com/verifereum/verifereum) includes instructions on how to build HOL4. The following commits are known to work for building the theories in this project:
  - HOL4: [e64fb78f42098918d99c7831ec2609e5ce47f77c](https://github.com/HOL-Theorem-Prover/HOL/tree/e64fb78f42098918d99c7831ec2609e5ce47f77c)
  - Verifereum: [4648cc50227c619eeffcdaa7393186549e11fa72](https://github.com/verifereum/verifereum/tree/4648cc50227c619eeffcdaa7393186549e11fa72)
