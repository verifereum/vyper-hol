# Vyper-HOL
Formal semantics for the [Vyper](https://vyperlang.org) programming language for [Ethereum](https://ethereum.org) in the [HOL4 theorem prover](https://hol-theorem-prover.org).

This work is part of the ongoing [Verifereum](https://verifereum.org) project building formal specifications and infrastructure for formal verification of Ethereum applications. Vyper is a compelling choice of programming language for secure smart contracts because of its clean design and focus on simplicity and readability. Formal semantics for Vyper, as pursued here, serves as a rigorous precise mathematical specification of the language and as an essential requirement for building a formally verified compiler from Vyper to EVM (Ethereum virtual machine) bytecode (and/or formally verifying the official Vyper compiler).

Initial development for the subset of Vyper covered here was supported by Grant ID FY25-1892 from the Ethereum Foundation's [Ecosystem Support Program](https://esp.ethereum.foundation). The project is active and evolving, with ongoing work to expand coverage and improve the toolchain.

## Contents

This repository contains a _formal_ and _executable_ definition of a subset of the semantics of Vyper, expressed as a _definitional interpreter_ in higher-order logic. This means we have defined an interpreter for Vyper programs as a mathematical function in logic, which can be executed and about which we can also prove theorems.

The work is presented as HOL4 theories: each theory, e.g. `vyperAST`, is implemented in a script file, e.g. `vyperASTScript.sml`.
These script files are intended to be read as a formal specification of Vyper (or at least the subset we have formalised so far), in addition to being executable by the HOL4 theorem prover to build the logical definitions and theories described.

The main function for executing Vyper statements is `eval_stmts` defined in `vyperInterpreter` (specifically `evaluate_def`). Top-level entry points are `load_contract` and `call_external`, defined in the same theory. Examples of calling these functions and executing the interpreter can be found in `vyperTestRunner`, which defines functions such as `run_call` used in evaluating the formal semantics on the Vyper language test suite.

The interpreter operates on abstract syntax (defined in `vyperAST`) and produces effects on an abstract machine state (`abstract_machine`, defined in `vyperInterpreter`) that represents the Ethereum virtual machine.

We describe the main contents and notable features of each theory in the repository below.

### vyperAST

The abstract syntax tree (AST) for Vyper is defined in `vyperAST`. The main datatypes are `expr` for expressions, `stmt` for statements, and `toplevel` for top-level declarations. This definition of Vyper's syntax is intended for use _after_ parsing, type-checking, constant and module inlining, and any other front-end elaboration done to user-written sources. As such, the syntax includes hints used by the interpreter, e.g., the `concat()` builtin is represented syntactically as `Concat n` where `n` is the type-inferrable maximum length of the result.

We syntactically restrict the targets for assignment statements/expressions, using the `assignment_target` type which can be seen as a restriction of the expression syntax to only variables (`x`), subscripting (`x[3]`), and attribute selection (`x.y`) with arbitrary nesting. This in particular also applies to the `append` and `pop` builtin functions on arrays, which are stateful (mutating) operations that we treat as assignments.

Interface declarations are not present in this AST because they are only needed for type-checking and hence not relevant for our purposes. Similarly, library imports and exports are not included.

### vyperInterpreter

The formal semantics for Vyper is defined in `vyperInterpreter`. The top-level entry-points are `load_contract` (for running a contract-deployment transaction given the Vyper source code of the contract), and `call_external` (for calling an external function of an already-deployed contract). These entry-points use the `eval_stmts` function defined in `evaluate_def` for interpreting Vyper code. These functions operate on Vyper values; see `vyperTestRunner` below for how to wrap these calls with encoding/decoding to ABI-encoded bytes.

The interpreter  in `evaluate_def` is written in a state-exception monad; the state contains the EVM machine state, Vyper-level globals in contracts, logs generated so far during execution, and the environment with variable bindings (since variables can be assigned to statefully). The non-stateful environment for the interpreter contains the stack of names of (internal) functions that have been called, information about the transaction that initiated the call, and the source code of existing contracts (including the current one). Exceptions are used for semantic errors (e.g., looking up a variable that was not bound, or in general attempting to interpret a badly-typed program), for legitimate runtime exceptions (e.g., failed assertions in user code, attempting to call a non-existent external function, etc.), and to manage control flow for internal function calls and loops (`return`, `break`, `continue`).

Termination is proved for the interpreter, validating Vyper's design as a total language (note, this does not rely on gas consumption, which is invisible at the Vyper source level). The termination argument uses the facts that internal function calls cannot recurse (even indirectly) and that all loops have an explicit (syntactic) bound.

At present external calls are not implemented. The plan is to define the semantics of external calls by deferring entirely to low-level EVM execution. This will make termination trivial since the interpreter will not be recursive for external calls. Ultimately in the case of external calls termination will then depend on gas consumption (and this being sufficient has already been proven in Verifereum).

### vyperSmallStep

This theory defines a continuation-passing version of the interpreter from `vyperInterpreter`, where each function in the interpreter takes a small step before returning a continuation. The small-step interpreter is proved equivalent to the normal (big-step) interpreter (theorem: `eval_cps_eq`).

The main purpose of the small-step interpreter is to make it easier to produce the executable version of the interpreter using HOL4's `cv_compute` mechanism. In particular, the relatively simple termination proofs for the small-step functions make the automatic translation via `cv_compute` work more smoothly.

### vyperABI

This theory defines conversions between Vyper types and the standard [Contract ABI](https://docs.soliditylang.org/en/latest/abi-spec.html) types used for most Ethereum smart contracts. These conversion functions are used when decoding the low-level call data supplied when calling functions in a Vyper contract, and for encoding the return value of a contract call. The `vyperABI` theory focuses on conversion between Vyper and ABI types, deferring to the ABI encoder/decoder in Verifereum for conversions to/from raw bytes.

### vyperTestRunner

This theory defines functions for re-running execution traces, as used in the Vyper test suite, using the Vyper-HOL definitional interpreter. The main entry-point is the `run_test` function. Machinery for decoding exported JSON test files and running them using the functions defined in `vyperTestRunner` is defined in the `vyperTestLib` library (and `vyperTestRunnerLib`). The library also includes functions for generating script files for running the tests; the generated files are visible in the `tests` subdirectory.

The decoding of JSON into our AST type is somewhat ad-hoc, in part because the JSON format is not fully specified. In future work, we might formalise more of the front-end or elaboration process, including parsing and type-checking, so that we can run source code directly. For now, we rely on an external front-end (e.g., as used in Vyper's test export process) and decode its output to construct terms in our formal syntax.

### vyperMisc

Some helper functions and theorems, some of which might eventually be upstreamed to the HOL repository.

## What is Missing

The focus of this work so far has been the core execution semantics of Vyper contract code, as abstract syntax, for external calls into a single contract. Therefore, the main limitations are _calls to other contracts_ (and other chain interaction like deploying contracts during execution), and _elaboration into abstract syntax_ done by the Vyper compiler front-end. Our intention is to remove all these limitations in future work to build a comprehensive and definitive formal semantics for the entire Vyper language.

Here are the specific aspects of Vyper that are currently not part of the formal model:

- Chain interaction
    - external contract calls (both `staticcall` and `extcall`) including `print`
    - [chain interaction bulitins](https://docs.vyperlang.org/en/latest/built-in-functions.html#chain-interaction) (`create_minimal_proxy_to`, etc.),
      except for `send` but including `@raw_return`
    - non-reentrancy checking
- Compiler front-end
    - concrete syntax, i.e., parsing
    - type-checking (the interpreter can fail during execution on badly-typed input)
    - interfaces, which are only relevant for type-checking
    - some cases of constant inlining (where, e.g., a literal value, not constant expression, is needed for the abstract syntax)
    - modules (`exports` and `import`)
    - internal and external functions with default arguments
- Miscellaneous builtins
    - some of the [cryptography builtins](https://docs.vyperlang.org/en/latest/built-in-functions.html#cryptography), especially involving elliptic curves
    - square root builtin: `sqrt`
    - builtins for raw calls: `abi_encode`, `abi_decode`, `method_id`
    - `blobhash`

## Outcomes, Challenges, and Next Steps

The main outcomes of this work so far are:
- We have defined a formal executable specification of a subset of Vyper in higher-order logic,
- which passes the `functional/codegen` section of the Vyper language test suite, modulo the exclusions listed above.

Passing a substantial portion of the official test suite means our formal semantics is a solid foundation for future work on formal verification for Vyper including both proving properties about the language and producing a verified compiler and other verified tools. In addition, we have proved some initial basic properties (in addition to the test executions), most notably, that the language is total (i.e., the interpreter always terminates).

It should also be noted that the export of the test suite in a format consumable by others was motivated in part by this project.

In achieving these outcomes, some of the technical details were more complex than expected. These include
- Assignment targets: in the official documentation for Vyper, as well as in the [Ivy interpreter](https://github.com/cyberthirst/ivy/) for Vyper, it can appear that the left-hand-sides of assignment operations (e.g., the `x[3].n` in `x[3].n = 9`) are arbitrary expressions. However, they are in fact a restricted subset (consider that `foo(x)[9] = 1` is invalid). This is made more explicit in our syntax, which has a separate syntactic category for assignment targets.
- The need for a small-step semantics for `cv_compute`, and the somewhat non-trivial termination argument for the semantics. The difficulty here was mostly due to pushing some of the edges of HOL4's libraries for defining functions and for providing fast execution for logical definitions.

Next steps (all can be done in parallel):
- Add the missing features listed above, primarily chain interaction. As mentioned earlier, we plan to add external calls by deferring to the underlying EVM semantics.
- Possibly revisit some of the design decisions in the semantics. For example, currently, runtime values carry some typing information (e.g., bit size for integers), but we could try leaving this information entirely in the syntax and not in the runtime values, which could simplify some operations like implicit casting.
- Formalise more of the front-end aspects of the language -- type-checking, modules, etc. -- noted as missing above.
- Start building a prototype for a verified compiler.

For a live roadmap and current tasks, see the [issue tracker](https://github.com/verifereum/vyper-hol/issues)

## Dependencies and How to Run

This work is developed in the [HOL4 theorem prover](https://hol-theorem-prover.org), and makes use of the Ethereum Virtual Machine (EVM) formalisation in the [Verifereum](https://verifereum.org) project, and the test suite for the [Vyper language](https://vyperlang.org) from [its repository](https://github.com/vyperlang/vyper). The following branches are used for active development:
  - HOL4: `master` (https://github.com/HOL-Theorem-Prover/HOL)
  - Verifereum: `main` (https://github.com/verifereum/verifereum)
  - Vyper: `main` (or the release branch matching the JSON test export you are using) (https://github.com/vyperlang/vyper)

The [Verifereum repository](https://github.com/verifereum/verifereum) includes instructions on how to build HOL4, and the Vyper repository includes its own installation instructions.

### Running the Vyper test suite

The test runner expects exported JSON fixtures to be available at `tests/vyper-test-exports`. You have two options:

1. **Use pre-exported fixtures** (preferred once available): clone https://github.com/vyperlang/vyperlang-tests and link it into `tests/vyper-test-exports`.
2. **Export locally from Vyper**: generate the fixtures from a Vyper checkout and link the export directory into `tests/vyper-test-exports`.

To run the Vyper test suite on our definitional interpreter, follow this approach:

1. Generate the Vyper tests using `pytest -s -n 1 --export tests/export -m "not fuzzing" tests/functional/codegen`.
2. Link the export directory into `tests/vyper-test-exports` (e.g., `ln -s ../vyper/tests/export tests/vyper-test-exports`).
3. Set the `VFMDIR` environment variable to a path of a clone of the Verifereum repository (tracking `main`).
4. `cd tests` and then run `Holmake`.

CI uses the same layout and will pull fixtures from `vyperlang-tests` when they are available.
