# Vyper-HOL
Formal semantics for the [Vyper](https://vyperlang.org) programming language for [Ethereum](https://ethereum.org) in the [HOL4 theorem prover](https://hol-theorem-prover.org).

This work is part of the ongoing [Verifereum](https://verifereum.org) project building formal specifications and infrastructure for formal verification of Ethereum applications. Vyper is a compelling choice of programming language for secure smart contracts because of its clean design and focus on simplicity and readability. Formal semantics for Vyper, as pursued here, serves as a rigorous precise mathematical specification of the language and as an essential requirement for building a formally verified compiler from Vyper to EVM (Ethereum virtual machine) bytecode (and/or formally verifying the official Vyper compiler).

Initial development for the subset of Vyper covered here was supported by Grant ID FY25-1892 from the Ethereum Foundation's [Ecosystem Support Program](https://esp.ethereum.foundation). The project is active and evolving, with ongoing work to expand coverage and improve the toolchain.

## Contents

This repository contains a _formal_ and _executable_ definition of a subset of the semantics of Vyper, expressed as a _definitional interpreter_ in higher-order logic. This means we have defined an interpreter for Vyper programs as a mathematical function in logic, which can be executed and about which we can also prove theorems.

The work is presented as HOL4 theories: each theory, e.g. `vyperAST`, is implemented in a script file, e.g. `vyperASTScript.sml`.
These script files are intended to be read as a formal specification of Vyper (or at least the subset we have formalised so far), in addition to being executable by the HOL4 theorem prover to build the logical definitions and theories described.

The main function for executing Vyper statements is `eval_stmts` defined in `vyperInterpreter` (specifically `evaluate_def`). Top-level entry points are `load_contract` and `call_external`, defined in the same theory. Examples of calling these functions and executing the interpreter can be found in `vyperTestRunner`, which defines functions such as `run_call` used in evaluating the formal semantics on the Vyper language test suite.

The interpreter operates on abstract syntax (defined in `vyperAST`) and an evaluation state (`evaluation_state`, defined in `vyperState`) representing the mutable EVM state. Top-level entry-points use an `abstract_machine` wrapper (defined in `vyperInterpreter`) that packages the evaluation state with contract source code and other static data.

## Repository Structure

The repository is organised into the following directories:

- **`syntax/`** — Vyper abstract syntax tree definitions
- **`frontend/`** — JSON import and translation into the core AST
- **`semantics/`** — Vyper semantics, organised across several theories covering values and types, value-level operations, storage encoding, ABI encoding, evaluation context and builtins, interpreter state and monad, the definitional interpreter itself, and a CPS/small-step version for efficient execution
  - **`semantics/prop/`** — Properties of the semantics (scope preservation, state preservation, etc.)
- **`tests/`** — Test infrastructure and generated test scripts from the Vyper test suite
- **`lowering/`** — Vyper-to-Venom IR compiler definition and correctness proofs
- **`venom/`** — Venom IR semantics and compiler pass proofs
  - **`venom/passes/`** — Individual compiler passes

We describe the main contents and notable features below.

### Syntax (`syntax/`)

The abstract syntax tree (AST) for Vyper is defined in `vyperAST`. The main datatypes are `expr` for expressions, `stmt` for statements, and `toplevel` for top-level declarations. This definition of Vyper's syntax is intended for use _after_ parsing, type-checking, constant and module inlining, and any other front-end elaboration done to user-written sources. As such, the syntax includes hints used by the interpreter, e.g., the `concat()` builtin is represented syntactically as `Concat n` where `n` is the type-inferrable maximum length of the result.

We syntactically restrict the targets for assignment statements/expressions, using the `assignment_target` type which can be seen as a restriction of the expression syntax to only variables (`x`), subscripting (`x[3]`), and attribute selection (`x.y`) with arbitrary nesting. This in particular also applies to the `append` and `pop` builtin functions on arrays, which are stateful (mutating) operations that we treat as assignments.

Interface declarations (`InterfaceDecl`) are included in the AST, with interface function signatures parsed from JSON and stored in the interpreter's type environment. This enables resolution of external calls to interface-typed targets. Full type-checking of interfaces remains future work (see [#47](https://github.com/verifereum/vyper-hol/issues/47)). Module imports and exports are handled by the JSON frontend/translation layer, and expressions carry `source_id` information to identify which module they belong to.

### Semantics (`semantics/`)

The formal semantics for Vyper is defined across several theories in `semantics/`. The top-level entry-points are `load_contract` (for running a contract-deployment transaction given the Vyper source code of the contract), and `call_external` (for calling an external function of an already-deployed contract). These entry-points use the `eval_stmts` function defined in `evaluate_def` for interpreting Vyper code. These functions operate on Vyper values; see the test infrastructure below for how to wrap these calls with encoding/decoding to ABI-encoded bytes.

`load_contract` is a Vyper-level deployment abstraction rather than a model of the EVM `CREATE` or `CREATE2` instructions. Its transaction supplies the target address directly, and successful deployment installs Vyper sources and exports. In contrast, Verifereum's EVM creation semantics derives the created address, updates creator and created-account nonces, executes init code, and installs runtime bytecode. Relating these two boundaries is an obligation of the Vyper-to-EVM compiler-correctness development. Vyper-level constructor value transfer is not omitted: it uses the ordinary external-function call path, retaining the updated accounts on success and rolling back to the input abstract machine on failure. A contract without an explicit `__init__` is represented by a synthetic empty payable constructor returned by `lookup_function`; it therefore follows the same path, including constant evaluation and deployment value transfer.

The semantics is organised into layers:
- **Values and types** — runtime values (`value`), type representations (`type_value`), and operations on values such as arithmetic, comparisons, conversions, and array manipulation.
- **Storage** — encoding and decoding of Vyper values to/from EVM storage slots, and hashmap slot computation using Keccak256.
- **ABI** — conversions between Vyper types and the standard [Contract ABI](https://docs.soliditylang.org/en/latest/abi-spec.html) encoding, used for encoding/decoding call data and return values. This defers to the ABI encoder/decoder in Verifereum for conversions to/from raw bytes.
- **Evaluation context** — the non-stateful environment for the interpreter, containing the transaction information, source code of existing contracts, and semantics for builtins that depend on this context (e.g., `msg.sender`, `block.number`, `ecrecover`).
- **Interpreter state** — the stateful machinery for the interpreter, including a state-exception monad, the mutable state (EVM accounts, variable scopes, immutables, logs, transient storage), and operations for reading/writing storage, variables, and globals. Assignment to nested targets (e.g., `x[3].n = 9`) is also handled at this level.
- **Interpreter** — the main definitional interpreter (`evaluate_def`), function lookup and calling conventions, the termination proof, and the top-level entry-points.
- **Type checking** — partial type-checking definitions (`vyperTypeCheck`), including `satisfies_type`, `well_typed_expr`, and related predicates.

The logical contract type checker can be evaluated on closed direct inputs, compiler JSON, or deployment traces using a reusable kernel-checked SML API. See the [contract checker evaluator guide](docs/check-contract-evaluator.md) for its trust model, interfaces, examples, and fixture-generation procedure.

The interpreter is written in a state-exception monad. Exceptions are used for semantic errors (e.g., looking up a variable that was not bound), legitimate runtime exceptions (e.g., failed assertions), and control flow for internal function calls and loops (`return`, `break`, `continue`).

Termination is proved for the interpreter, validating Vyper's design as a total language (this does not rely on gas consumption, which is invisible at the Vyper source level). The termination argument uses the facts that internal function calls cannot recurse (even indirectly) and that all loops have an explicit (syntactic) bound.

External calls (`staticcall` and `extcall`) are implemented by deferring to the low-level EVM execution defined in Verifereum. This makes termination straightforward since the interpreter is not recursive for external calls; termination depends on gas consumption (and this being sufficient has already been proven in Verifereum). The interpreter also supports module imports, with internal function calls across modules tracked via `source_id`, and `@deploy` functions callable during contract deployment.

Contract-creation builtins (`raw_create`, `create_copy_of`, `create_from_blueprint`, and minimal proxies) execute their initcode through Verifereum. Successful creation deposits the returned runtime code and retains constructor state and logs; failed creation restores the pre-endowment account state while retaining the creator nonce increment. The constructor sees a separate original-account snapshot in which its new address is empty, while the live account already has the creation nonce. Constructor `SELFDESTRUCT` therefore queues the new address for deletion at the successful transaction boundary, not during initcode execution. Constructor `REVERT` bytes are propagated when `revert_on_failure` is enabled. The test runner initializes source-deployed and blueprint accounts with nonce one, matching the EVM state visible to subsequent `CREATE` instructions.

A continuation-passing (small-step) version of the interpreter is also defined and proved equivalent to the big-step version. Its main purpose is to facilitate efficient execution via HOL4's `cv_compute` mechanism.

Properties of the semantics — such as scope preservation and state preservation — are proved in `semantics/prop/`.

### Tests (`tests/`)

The test infrastructure defines functions for re-running execution traces from the Vyper test suite using the definitional interpreter. The main entry-point is the `run_test` function defined in `vyperTestRunner`. Machinery for decoding exported JSON test files is defined in the `vyperTestLib` library; the generated test scripts are in `tests/generated/`.

The decoding of JSON into our AST type is somewhat ad-hoc, in part because the JSON format is not fully specified. In future work, we might formalise more of the front-end or elaboration process, including parsing and type-checking, so that we can run source code directly. For now, we rely on an external front-end (e.g., as used in Vyper's test export process) and decode its output to construct terms in our formal syntax. Compiler-folded `method_id` keyword values are retained when decoding `_abi_encode`, preserving selector-prefixed calldata in source replays.

## Current Limitations

The formal semantics covers the core Vyper language including external calls (`staticcall`, `extcall`), reentrancy protection (`@nonreentrant`), `raw_call`, contract creation builtins, transient storage, and module imports. The main limitation is the **front-end**: there is no formal parser (we operate on abstract syntax exported as JSON, [#46](https://github.com/verifereum/vyper-hol/issues/46)) and type-checking is partial ([#47](https://github.com/verifereum/vyper-hol/issues/47)). A small number of minor features remain unimplemented, including `print` and gas modelling for `msg.gas`/`msg.mana` and external call gas limits ([#98](https://github.com/verifereum/vyper-hol/issues/98)).

## Outcomes and Next Steps

The main outcomes of this work so far are:
- We have defined a formal executable specification of a subset of Vyper in higher-order logic,
- which passes the `functional/codegen` section of the Vyper language test suite, modulo the minor exclusions listed above.

Passing a substantial portion of the official test suite means our formal semantics is a solid foundation for future work on formal verification for Vyper including both proving properties about the language and producing a verified compiler and other verified tools. In addition to the test executions, we have proved a number of properties about the semantics, including totality of the language (the interpreter always terminates), scope and state preservation properties for the evaluator (in `semantics/prop/`), and correctness proofs for several Venom IR compiler passes (in `venom/passes/`). The `lowering/` directory contains a Vyper-to-Venom IR compiler definition with end-to-end correctness proofs in progress.

It should also be noted that the export of the test suite in a format consumable by others was motivated in part by this project.

Next steps include formalising the front-end (parsing and full type-checking), proving safety properties about the language ([#90](https://github.com/verifereum/vyper-hol/issues/90)), and continuing work on verifying the Vyper compiler. For a live roadmap and current tasks, see the [issue tracker](https://github.com/verifereum/vyper-hol/issues).

## Dependencies and How to Run

This work is developed in the [HOL4 theorem prover](https://hol-theorem-prover.org), and makes use of the Ethereum Virtual Machine (EVM) formalisation in the [Verifereum](https://verifereum.org) project, and the test suite for the [Vyper language](https://vyperlang.org) from [its repository](https://github.com/vyperlang/vyper).

The project is built with [`holbuild`](https://github.com/charles-cooper/holbuild). The repository's `holproject.toml` is the source of truth for the project configuration and pinned HOL dependencies, including the compatible [Verifereum](https://github.com/verifereum/verifereum) revision. Vyper functional tests are generated from the upstream commit pinned in [`VYPER_PIN`](VYPER_PIN). The CI workflow (`.github/workflows/holbuild.yml`) is the recommended reference for the exact automated build.

For a local build, install `holbuild` v0.10.0 or newer and run:

```bash
holbuild buildhol
holbuild -j"$(nproc)" build
```

`holbuild buildhol` builds and caches the HOL toolchain and project dependencies specified by `holproject.toml`.

Release instructions, including the prebuilt holbuild archive artefact, are in [docs/release.md](docs/release.md).

### Running the Vyper test suite

The test runner expects exported JSON fixtures at `tests/vyper-test-exports`.
`tests/semantics-profile.json` selects Venom, `--optimize none`, Prague and the
revm execution backend explicitly. The upstream harness enables decimals and
bytecode metadata and disables compiler debugging by default. Individual tests
can override compiler settings or source pragmas; each export's `.provenance`
sidecar records the resolved settings for every deployment, including legacy or
raw-bytecode deployments. Those overrides remain part of the upstream test.
The upstream JSON does not record per-test execution-backend or metadata
overrides; the profile records their harness defaults, not a claim that every
deployment uses them.

The semantics EVM target follows the newest fork supported by `VYPER_PIN`.
The export plugin rejects an older run target, so a repin adding a newer fork
requires updating the explicit profile and regenerating exports. Per-test
compiler overrides remain supported.

The export plugin preserves exact revm runtime bytes. Upstream's `get_code`
strips all trailing zeros, which loses real STOP/data bytes as well as revm's
analysis padding. The plugin removes only padding verified against the account's
code hash when recording deployment traces; upstream test-facing calls are
unchanged. HOL's exact runtime-byte comparison remains enabled.

The compiler bytecode oracle has its own profile in
`lowering/defs/bytecode/python_o1_bytecode_oracle.py`: Venom/NONE/Prague with
metadata disabled and decimals enabled by fixture pragmas. These profiles can
evolve independently. At this pin NONE runs the O1 Venom passes but disables
assembly optimisation; it is not `-O O1`. Both compile for Prague (the newest
target the pin supports), whereas the HOL EVM semantics executes Osaka.
Metadata need not match for behavioral replay. Bytecode parity is opt-in and
is not implied by a passing semantics replay.

Use Python 3.11.11 in an isolated environment, then run from this repository:

```bash
git clone --depth 1 https://github.com/vyperlang/vyper.git vyper-src
cd vyper-src
git fetch --unshallow --tags
git checkout --detach "$(tr -d '[:space:]' < ../VYPER_PIN)"
git config core.abbrev 8
SETUPTOOLS_SCM_PRETEND_VERSION_FOR_VYPER=0.5.0a4+cd74ce4f \
  PIP_CONSTRAINT="../tests/semantics-test-constraints.txt ../tests/semantics-build-constraints.txt" \
  pip install . --group test
cd ..
python tools/vyper_test_exports.py generate \
  --vyper-repo vyper-src --output tests/vyper-test-exports
```

The generator requires a clean pinned checkout, checks Python/package versions,
and refuses an existing output directory so an incremental export cannot leave
stale tests behind. Use repeated `--test tests/.../test_file.py::test_name`
arguments for focused exports. It writes provenance only after pytest succeeds.
Default full-suite exports temporarily include `tests/vyper-regression` in the
upstream harness; focused `--test`/`--fixture` exports do not. Regression Python
sources participate in both cache invalidation and provenance checks.
Replay checks each file's hash and provenance against the pin, profile,
constraints, generator and setup action; CI's export cache key covers those
same inputs. A profile or generator change requires regeneration, including
the committed exports under `tests/fixtures/exports`. Keep their sidecars.

From the Vyper-HOL repository root, generate the HOL test wrappers from those exports:

```bash
holbuild build vyperTestLib
generator=$(mktemp --suffix=.sml)
trap 'rm -f "$generator"' EXIT
printf '%s\n' 'vyperTestLib.generate_tests ();' > "$generator"
(cd tests && holbuild run --noconfig vyperTestLib "$generator")
```

Then run individual generated test theories with `holbuild`, for example:

```bash
holbuild -j"$(nproc)" build vyperTest_functional_builtins_codegen_test_abi_decodeTheory
```

The CI workflow runs the generated tests in parallel groups; see `.github/workflows/holbuild.yml` for that full setup.

Local semantic regressions live as behavior-named pytests in
[`tests/vyper-regression`](tests/vyper-regression/README.md). The pinned export
includes them in the same cache and CI matrix as the upstream tests; exported
traces and local generated wrappers are not versioned. Each enabled regression
lands with the fix that makes it pass.

The `vyperTestCoverageReportTheory` target derives `tests/vyper-coverage-report.txt` from the raw exported JSON; CI builds the target and prints the report. Its per-file and aggregate `[vyper-coverage]` summaries report exported items, fixtures and other non-test items, selected tests, direct and fixture-expanded trace counts, name and source-pattern exclusions, items with no exported traces, traceful items whose source is missing or supplied only by fixtures, unreferenced traced fixtures, malformed items, and files with no selected tests. It deliberately does not decode traces into HOL terms. Generated definitions theories additionally report successfully decoded traces and decode failures while performing their normal builds. Individual exclusion lines record the test name and selection reason. All these messages are reporting only: existing selection rules and decode-failure enforcement are unchanged.
