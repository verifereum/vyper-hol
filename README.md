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

## Repository Structure

The repository is organised into the following directories:

- **`syntax/`** — Vyper abstract syntax tree definitions
- **`frontend/`** — JSON import and parsing
- **`semantics/`** — Vyper semantics, organised across several theories covering values and types, value-level operations, storage encoding, ABI encoding, evaluation context and builtins, interpreter state and monad, the definitional interpreter itself, and a CPS/small-step version for efficient execution
  - **`semantics/prop/`** — Properties of the semantics (scope preservation, state preservation, etc.)
- **`tests/`** — Test infrastructure and generated test scripts from the Vyper test suite
- **`venom/`** — Venom IR semantics and compiler pass proofs
  - **`venom/passes/`** — Individual compiler passes

We describe the main contents and notable features below.

### Syntax (`syntax/`)

The abstract syntax tree (AST) for Vyper is defined in `vyperAST`. The main datatypes are `expr` for expressions, `stmt` for statements, and `toplevel` for top-level declarations. This definition of Vyper's syntax is intended for use _after_ parsing, type-checking, constant and module inlining, and any other front-end elaboration done to user-written sources. As such, the syntax includes hints used by the interpreter, e.g., the `concat()` builtin is represented syntactically as `Concat n` where `n` is the type-inferrable maximum length of the result.

We syntactically restrict the targets for assignment statements/expressions, using the `assignment_target` type which can be seen as a restriction of the expression syntax to only variables (`x`), subscripting (`x[3]`), and attribute selection (`x.y`) with arbitrary nesting. This in particular also applies to the `append` and `pop` builtin functions on arrays, which are stateful (mutating) operations that we treat as assignments.

Interface declarations (`InterfaceDecl`) are included in the AST, with interface function signatures parsed from JSON and stored in the interpreter's type environment. This enables resolution of external calls to interface-typed targets. Full type-checking of interfaces remains future work (see [#47](https://github.com/verifereum/vyper-hol/issues/47)). Module imports and exports are supported: the AST includes `ImportDecl` and `ExportsDecl` top-level declarations, and expressions carry `source_id` information to identify which module they belong to.

### Semantics (`semantics/`)

The formal semantics for Vyper is defined across several theories in `semantics/`. The top-level entry-points are `load_contract` (for running a contract-deployment transaction given the Vyper source code of the contract), and `call_external` (for calling an external function of an already-deployed contract). These entry-points use the `eval_stmts` function defined in `evaluate_def` for interpreting Vyper code. These functions operate on Vyper values; see the test infrastructure below for how to wrap these calls with encoding/decoding to ABI-encoded bytes.

The semantics is organised into layers:
- **Values and types** — runtime values (`value`), type representations (`type_value`), and operations on values such as arithmetic, comparisons, conversions, and array manipulation.
- **Storage** — encoding and decoding of Vyper values to/from EVM storage slots, and hashmap slot computation using Keccak256.
- **ABI** — conversions between Vyper types and the standard [Contract ABI](https://docs.soliditylang.org/en/latest/abi-spec.html) encoding, used for encoding/decoding call data and return values. This defers to the ABI encoder/decoder in Verifereum for conversions to/from raw bytes.
- **Evaluation context** — the non-stateful environment for the interpreter, containing the transaction information, source code of existing contracts, and semantics for builtins that depend on this context (e.g., `msg.sender`, `block.number`, `ecrecover`).
- **Interpreter state** — the stateful machinery for the interpreter, including a state-exception monad, the mutable state (EVM accounts, variable scopes, immutables, logs, transient storage), and operations for reading/writing storage, variables, and globals. Assignment to nested targets (e.g., `x[3].n = 9`) is also handled at this level.
- **Interpreter** — the main definitional interpreter (`evaluate_def`), function lookup and calling conventions, the termination proof, and the top-level entry-points.

The interpreter is written in a state-exception monad. Exceptions are used for semantic errors (e.g., looking up a variable that was not bound), legitimate runtime exceptions (e.g., failed assertions), and control flow for internal function calls and loops (`return`, `break`, `continue`).

Termination is proved for the interpreter, validating Vyper's design as a total language (this does not rely on gas consumption, which is invisible at the Vyper source level). The termination argument uses the facts that internal function calls cannot recurse (even indirectly) and that all loops have an explicit (syntactic) bound.

External calls (`staticcall` and `extcall`) are implemented by deferring to the low-level EVM execution defined in Verifereum. This makes termination straightforward since the interpreter is not recursive for external calls; termination depends on gas consumption (and this being sufficient has already been proven in Verifereum). The interpreter also supports module imports, with internal function calls across modules tracked via `source_id`, and `@deploy` functions callable during contract deployment.

A continuation-passing (small-step) version of the interpreter is also defined and proved equivalent to the big-step version. Its main purpose is to facilitate efficient execution via HOL4's `cv_compute` mechanism.

Properties of the semantics — such as scope preservation and state preservation — are proved in `semantics/prop/`.

### Tests (`tests/`)

The test infrastructure defines functions for re-running execution traces from the Vyper test suite using the definitional interpreter. The main entry-point is the `run_test` function defined in `vyperTestRunner`. Machinery for decoding exported JSON test files is defined in the `vyperTestLib` library; the generated test scripts are in `tests/generated/`.

The decoding of JSON into our AST type is somewhat ad-hoc, in part because the JSON format is not fully specified. In future work, we might formalise more of the front-end or elaboration process, including parsing and type-checking, so that we can run source code directly. For now, we rely on an external front-end (e.g., as used in Vyper's test export process) and decode its output to construct terms in our formal syntax.

## What is Missing

The focus of this work so far has been the core execution semantics of Vyper contract code, as abstract syntax, for external calls into a single contract. Therefore, the main limitations are _calls to other contracts_ (and other chain interaction like deploying contracts during execution), and _elaboration into abstract syntax_ done by the Vyper compiler front-end. Our intention is to remove all these limitations in future work to build a comprehensive and definitive formal semantics for the entire Vyper language.

Here are the specific aspects of Vyper that are currently not part of the formal model:

- Chain interaction ([#37](https://github.com/verifereum/vyper-hol/issues/37))
    - external contract calls: `staticcall`, `extcall`, and `extcall` with `value=` (sending ETH) are implemented, but the `gas=` parameter is not yet supported; `default_return_value=` is supported ([#38](https://github.com/verifereum/vyper-hol/issues/38))
    - `print` (which uses external calls under the hood) ([#38](https://github.com/verifereum/vyper-hol/issues/38))
    - gas modeling for `msg.gas` and external call gas limits ([#98](https://github.com/verifereum/vyper-hol/issues/98))
    - [chain interaction builtins](https://docs.vyperlang.org/en/latest/built-in-functions.html#chain-interaction) (`create_minimal_proxy_to`, `create_copy_of`, `create_from_blueprint`, `raw_call`, etc.) and `@raw_return` ([#39](https://github.com/verifereum/vyper-hol/issues/39))
    - non-reentrancy checking (`@nonreentrant`) ([#40](https://github.com/verifereum/vyper-hol/issues/40))
- Compiler front-end
    - concrete syntax, i.e., parsing ([#46](https://github.com/verifereum/vyper-hol/issues/46))
    - type-checking (the interpreter can fail during execution on badly-typed input) ([#47](https://github.com/verifereum/vyper-hol/issues/47))
    - some constant expression evaluation is still performed by the JSON front-end rather than formally; formalising this processing is tracked in [#135](https://github.com/verifereum/vyper-hol/issues/135)

## Outcomes, Challenges, and Next Steps

The main outcomes of this work so far are:
- We have defined a formal executable specification of a subset of Vyper in higher-order logic,
- which passes the `functional/codegen` section of the Vyper language test suite, modulo the exclusions listed above.

Passing a substantial portion of the official test suite means our formal semantics is a solid foundation for future work on formal verification for Vyper including both proving properties about the language and producing a verified compiler and other verified tools. In addition to the test executions, we have proved a number of properties about the semantics, including totality of the language (the interpreter always terminates), scope and state preservation properties for the evaluator (in `semantics/prop/`), and correctness of two Venom IR compiler passes (phi elimination and revert-to-assert, in `venom/passes/`).

It should also be noted that the export of the test suite in a format consumable by others was motivated in part by this project.

In achieving these outcomes, some of the technical details were more complex than expected. These include
- Assignment targets: in the official documentation for Vyper, as well as in the [Ivy interpreter](https://github.com/cyberthirst/ivy/) for Vyper, it can appear that the left-hand-sides of assignment operations (e.g., the `x[3].n` in `x[3].n = 9`) are arbitrary expressions. However, they are in fact a restricted subset (consider that `foo(x)[9] = 1` is invalid). This is made more explicit in our syntax, which has a separate syntactic category for assignment targets.
- The need for a small-step semantics for `cv_compute`, and the somewhat non-trivial termination argument for the semantics. The difficulty here was mostly due to pushing some of the edges of HOL4's libraries for defining functions and for providing fast execution for logical definitions.

Next steps (all can be done in parallel):
- Complete remaining external call features: `gas=` parameter, `print`, and gas modeling ([#38](https://github.com/verifereum/vyper-hol/issues/38), [#98](https://github.com/verifereum/vyper-hol/issues/98)).
- Add remaining chain interaction features: `@nonreentrant`, `raw_call`, contract creation builtins ([#39](https://github.com/verifereum/vyper-hol/issues/39), [#40](https://github.com/verifereum/vyper-hol/issues/40)).
- Prove safety properties about the language: arithmetic safety, array bounds, type preservation, etc. ([#90](https://github.com/verifereum/vyper-hol/issues/90)).
- Possibly revisit some of the design decisions in the semantics. For example, currently, runtime values carry some typing information (e.g., bit size for integers), but we could try leaving this information entirely in the syntax and not in the runtime values, which could simplify some operations like implicit casting ([#45](https://github.com/verifereum/vyper-hol/issues/45)).
- Formalise more of the front-end aspects of the language -- type-checking, parsing, etc. -- noted as missing above.
- Continue work on verifying the Vyper compiler.

For a live roadmap and current tasks, see the [issue tracker](https://github.com/verifereum/vyper-hol/issues)

## Dependencies and How to Run

This work is developed in the [HOL4 theorem prover](https://hol-theorem-prover.org), and makes use of the Ethereum Virtual Machine (EVM) formalisation in the [Verifereum](https://verifereum.org) project, and the test suite for the [Vyper language](https://vyperlang.org) from [its repository](https://github.com/vyperlang/vyper). The following branches are used for active development:
  - HOL4: `master` (https://github.com/HOL-Theorem-Prover/HOL)
  - Verifereum: `main` (https://github.com/verifereum/verifereum)
  - Vyper: `main` (or the release branch matching the JSON test export you are using) (https://github.com/vyperlang/vyper)

The [Verifereum repository](https://github.com/verifereum/verifereum) includes instructions on how to build HOL4, and the Vyper repository includes its own installation instructions.

### Running the Vyper test suite

The test runner expects exported JSON fixtures to be available at `tests/vyper-test-exports`.
The exported fixtures are obtained using the Vyper repository.
To run the Vyper test suite on our definitional interpreter, follow this approach:

1. Generate the Vyper tests using `pytest -s -n0 --export tests/export -m "not fuzzing" tests/functional`.
2. Link the export directory into `tests/vyper-test-exports` (e.g., `ln -s ../vyper/tests/export tests/vyper-test-exports`).
3. Set the `VFMDIR` environment variable to a path of a clone of the Verifereum repository (tracking `main`).
4. `cd tests/generated` and then run `Holmake`.

CI uses the same layout and currently exports fixtures from a Vyper checkout during the workflow run.
