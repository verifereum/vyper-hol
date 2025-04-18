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

The HOL4 script files that produce the formal theories are all in the root of the repository. We describe the main idea and contents of each theory as follows:

### vyperAst

The abstract syntax tree (AST) for Vyper is defined in `vyperAstScript.sml`. The main datatypes are `expr` for expressions, `stmt` for statements, and `toplevel` for top-level declarations.

We syntactically restrict the targets for assignment statements/expressions, using the `assignment_target` type which can be seen as a restriction of the expression syntax to only variables (`x`), subscripting (`x[3]`), and attribute selection (`x.y`) with arbitrary nesting. This in particular also applies to the `append` and `pop` builtin functions on arrays, which are stateful (mutating) operations that we treat as assignments.

### vyperInterpreter

The formal semantics for Vyper is defined in `vyperInterpreterScript.sml`. The top-level entry-points are `load_contract` (for running a contract-deployment transaction given the Vyper source code of the contract), and `call_external` (for calling an external function of an already-deployed contract). These entry-points use the `eval_stmts` function defined in `evaluate_def` for interpreting Vyper code.

The interpreter  in `evaluate_def` is written in a state-exception monad; the state contains the EVM machine state, Vyper-level globals in contracts, logs generated so far during execution, and the environment with variable bindings (since variables can be assigned to statefully). The non-stateful environment for the interpreter contains the stack of names of (internal) functions that have been called, information about the transaction that initiated the call, and the source code of existing contracts (including the current one). Exceptions are used for semantic errors (e.g., looking up a variable that was not bound, or in general attempting to interpret a badly-typed program), for legitimate runtime exceptions (e.g., failed assertions in user code, attempting to call a non-existent external function, etc.), and to manage control flow for internal function calls and loops (`return`, `break`, `continue`).

Termination is proved for the interpreter, validating Vyper's design as a total language (n.b., this does not rely on gas consumption, which is invisible at the Vyper source level). The termination argument uses the facts that internal function calls cannot recurse (even indirectly) and that all loops have an explicit (syntactic) bound.

At present external calls are not implemented, and when they are added they could pose a problem for the termination argument above. Our plan is to define the semantics of external calls by deferring entirely to low-level EVM execution. This will make termination trivial since the interpreter will not be recursive for external calls. Ultimately in the case of external calls termination will then depend on gas consumption (and this being sufficient has already been proven in Verifereum).

### vyperSmallStep

This theory defines a continuation-passing version of the interpreter from `vyperInterpreterTheory`, where each function in the interpreter takes a small step before returning a continuation. The small-step interpreter is proved equivalent to the normal (big-step) interpreter (theorem: `eval_cps_eq`).

The main purpose of the small-step interpreter is to make it easier to produce the executable version of the interpreter using HOL4's `cv_compute` mechanism. In particular, the relatively simple termination proofs for the small-step functions make the automatic translation via `cv_compute` work more smoothly.

### vyperTest

This theory proves theorems (by execution in logic) stating that the formal semantics passes each of the tests in the Ivy Vyper interpreter's [end-to-end test suite](https://github.com/cyberthirst/ivy/blob/aae6aa671e3dc6106708d992f34d3b1b61c45bbe/tests/test_e2e.py), for the tests that are applicable to the subset of the language formalised.

The test code is loaded at a fixed contract address from a fixed sender address for these tests, because a fully concrete machine state is required for our approach to fast execution in logic.

There is also a `vyperDemo` theory that has some initial steps towards defining a larger contract and proving some properties about it at the level of its Vyper source code.

## Dependencies

This work is developed in the [HOL4 theorem prover](https://hol-theorem-prover.org), and makes use of the Ethereum Virtual Machine (EVM) formalisation in the [Verifereum](https://verifereum.org) project. The [Verifereum repository](https://github.com/verifereum/verifereum) includes instructions on how to build HOL4. The following commits are known to work for building the theories in this project:
  - HOL4: [e64fb78f42098918d99c7831ec2609e5ce47f77c](https://github.com/HOL-Theorem-Prover/HOL/tree/e64fb78f42098918d99c7831ec2609e5ce47f77c)
  - Verifereum: [4648cc50227c619eeffcdaa7393186549e11fa72](https://github.com/verifereum/verifereum/tree/4648cc50227c619eeffcdaa7393186549e11fa72)
