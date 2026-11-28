## Summary

vyper-hol proves, in the HOL4 theorem prover, that Vyper contracts compiled
by its compiler definition behave on the EVM the way the Vyper source says
they should. Four theorems state this for a single-module contract:

- **Deployment correctness**
  ([`e2e_deploy_correctness_deployed`](#thm-e2eDeployed-e2e_deploy_correctness_deployed)):
  when its hypotheses hold, running the compiled deployment bytecode
  either stops by starvation (below) or gives the constructor's result,
  and then, if the constructor succeeded and the new account isn't
  scheduled for deletion, it has installed a contract that the call
  theorems apply to.
- **Call correctness**
  ([`vyper_call_correct_deployed`](#thm-e2eDeployed-vyper_call_correct_deployed)):
  a later call to that contract, with any calldata, either gives the
  result the source semantics gives or stops by starvation (below), when
  the call's own hypotheses hold; and, when it is the only frame running
  and the contract isn't scheduled for deletion, the contract is still
  deployed for the next call, and its storage still meets the storage
  hypothesis.
- **Gas sufficiency for deployment and for calls**
  ([`e2e_deploy_gas_sufficient`](#thm-e2eGasSufficientTop-e2e_deploy_gas_sufficient),
  [`vyper_call_gas_sufficient_deployed`](#thm-e2eDeployed-vyper_call_gas_sufficient_deployed)):
  starvation (below) by running out of gas is avoidable: with enough gas,
  the compiled code doesn't run out of gas, provided the larger-gas run
  meets the storage and call-trace conditions and the source doesn't stop
  with one of a few listed errors; a deployment may still run out when its
  runtime code exceeds the EVM's code-size limit. Starvation by stack
  overflow is ruled out when the code passes the static stack check.

All four are proved with no admitted steps at the commit this page was
built from: `holbuild check` reports each one clean. Each theorem is
stated in full below the words that explain it, with every hypothesis and,
at the end of the page, the definitions they rest on. The explanations
simplify: where they and the statements differ, the statements are what
is proved.

## What is being related

A **source semantics** and an **EVM semantics**, both written in HOL4 as
executable functions:

- The Vyper semantics is vyper-hol's definitional interpreter. A contract is
  its list of top-level declarations (`tops`), which vyper-hol's own
  frontend translates from the annotated AST that Vyper's parser and type
  checker produce. The frontend evaluates compile-time constants itself,
  from their source expressions, rather than taking Vyper's folded values.
  `load_contract`
  runs the constructor and `call_external` runs one external call. The
  interpreter is tested against Vyper's own test suite.
- The EVM semantics is [Verifereum](https://github.com/verifereum/verifereum)'s
  (`run_call` runs one call frame to completion, nested calls included),
  tested against the Ethereum execution spec tests.

The compiler is the HOL function
[`compile_vyper fin policy tops`](#nx-compileVyper-compile_vyper),
which returns the deployment bytecode and the runtime bytecode, or nothing
if it refuses the contract. It lowers Vyper to Venom, Vyper's intermediate
representation, runs the Venom passes of Vyper's `-O1` pipeline, and
generates EVM assembly and bytecode. `fin` is the last step on the assembly:
either nothing, or the assembly optimizer
([`accepted_finalizers`](#def-asmOptimizer-accepted_finalizers)).
`policy` is any compiler setting. The definition follows the Vyper compiler
at the commit in the repository's `VYPER_PIN`, and the two are compared
byte for byte on test contracts; the theorems are about this definition,
not about the Python program.

External calls are where the contract meets code it doesn't control. The
source semantics does not run other contracts: it reads what each external
call (or contract creation) returned from the EVM run's own **call trace**,
`call_trace es`. When the run succeeds, the theorems then say the
compiled code made the same calls as the source, in the same order and
with the same targets, values and data; when it fails, they constrain
only how the frame fails.

Gas is the other value the source can't compute: `msg.gas` depends on the
compiled code. The source takes each `msg.gas` from a list of **gas
readings**
([`gas_readings_rel`](#def-e2eDefs-gas_readings_rel)): the
theorems match some of the source's readings to values the EVM's `GAS`
instructions returned, not necessarily in the same order, and the result
holds for every list of readings consistent with that matching, the
unmatched ones taking any value. Gas forwarded to a call is not a
reading: when the source call gives a `gas=` amount, the compiled call
passes that amount as the call instruction's gas operand (the EVM may
give the callee less, under its own cap on forwarded gas); otherwise the
operand is not constrained.

## What the hypotheses ask of the caller

Each theorem's hypotheses are listed below its statement, with a
plain-language note on each. In groups:

- **The compiler accepted the contract.** `compile_vyper` returned bytecode,
  with one of the accepted finalizers.
- **The contract type-checks.** vyper-hol's own contract checker
  (`check_contract`) accepts it, and the source state and transaction are
  well typed: values fit their types and machine words. This is a check the
  theorem's user runs on their contract, by evaluation in HOL.
- **The EVM starts where the source starts.** A fresh frame (for deployment,
  a fresh creation frame) whose caller, callee, value, calldata and block
  fields match the source transaction, after the value transfer, and an
  EVM state with in-range balances and buffers. For a call, the code it runs
  is the code installed at the target.
- **Bounded call trace.** Fewer than 2⁶⁴ external calls are observed.
- **A fixed set of storage regions, `H`.** Vyper places `HashMap` entries at
  keccak-derived slots. Rather than assume keccak never collides, the
  theorems take a finite list of storage regions and nonreentrancy lock
  slots. They require each region to fit in the slot space, distinct
  regions of the same kind not to overlap, transient regions to avoid the
  lock slots, for a call, the source's initial storage to decode on the
  regions ([`storage_ok`](#def-e2eCorrectness-storage_ok);
  deployment doesn't assume it, and establishes it for later calls), and the
  source run, for every gas filling, to keep within them: every storage
  region it uses is in `H`, every lock it takes is in the lock list, and
  every storage it takes back from a called contract decodes on the
  regions ([`call_within`](#def-e2eCorrectness-call_within),
  [`deploy_within`](#def-e2eDeployEntry-deploy_within)).
  The contract's storage and transient storage then agree with the
  source's at every byte except the unused bytes of a value's layout in a
  region the run touched; other accounts agree exactly.

## Deployment correctness

When the hypotheses below hold, the EVM runs the deployment bytecode
followed by the ABI-encoded constructor arguments, in a fresh creation
frame. Then the run finishes, and either the frame is **starved** (below),
or:

- the result matches the source constructor's
  ([`deploy_result_rel_at`](#def-e2eDeployed-deploy_result_rel_at)):
  on success the account holds the runtime bytecode followed by the
  encoded immutables (or, if the constructor self-destructs, no code and
  the account is scheduled for deletion), and balances, storage,
  transient storage, logs and the calls the constructor made all agree
  with the source's; when the
  source constructor fails, the frame fails as described for calls below; and
- on success, unless the new account is scheduled for deletion, the
  contract is [`deployed`](#def-e2eDeployed-deployed) at its address,
  and its storage satisfies the call theorems' storage hypothesis.

`deployed` is exactly what the call theorems assume about the installed
contract, so the two compose: the call theorems apply to each later call
whose own hypotheses (below) hold, and the call correctness theorem
concludes that the contract stays deployed for the call after it. The
deployment's next source state
([`next_source_machine`](#def-e2eDefs-next_source_machine))
is the source's result with the EVM run's accounts after deletions, and
with transient storage, logs and pending deletions cleared.

<!-- dossier: thm-e2eDeployed-e2e_deploy_correctness_deployed -->

## Call correctness

For a deployed contract and any transaction to it, with any calldata,
when the hypotheses below hold, the EVM run of the call frame finishes,
and either the frame is starved, or
([`calldata_result_rel`](#def-e2eCorrectness-calldata_result_rel)):

- if the calldata selects no function, the frame reverts with empty
  return data. That is the case when a selector matching no function, or
  calldata shorter than four bytes, meets a contract without
  `__default__`, and when the calldata is too short for the selected
  function's arguments or they don't decode
  ([`calldata_dispatch`](#def-vyperCalldata-calldata_dispatch));
- otherwise the result matches the source semantics' run of the selected
  function ([`call_result_rel_at`](#def-e2eDefs-call_result_rel_at)):
  - a normal return gives the ABI encoding of the returned value as return
    data (for a `@raw_return` function, the returned bytes themselves),
    with the same balances, storage, transient storage, logs and
    outgoing calls;
  - `selfdestruct` halts with the same effects;
  - a failed `assert` or a `raise` reverts (with `UNREACHABLE` the frame may
    fail in any way), and so does a revert passed on from a called contract; any
    other runtime error of the source (an overflow, an index out of bounds)
    makes the frame fail. The revert data itself is not compared.

Whether or not the frame starved, when the call is the only frame running
and the contract is not scheduled for deletion afterwards, the contract is
still `deployed` in the world the call leaves
([`transaction_world`](#def-e2eTransactionWorld-transaction_world)):
after a successful call, the state before it with the EVM run's accounts
after deletions and with transient storage, logs and pending deletions
cleared; after a failed one, the state before the call. The storage
hypothesis holds there for every later call to the contract. So the call
theorems apply again to the next call, whose other hypotheses still have
to hold.

<!-- dossier: thm-e2eDeployed-vyper_call_correct_deployed -->

## Gas sufficiency

Each correctness theorem allows the run to stop by **starvation**
([`frame_starved`](#def-e2eDeployed-frame_starved)): the frame
ran out of gas, or overflowed the EVM stack in code that fails a static
stack-height check (`bytecode_stack_check`); so when the code passes that
check, starvation can only be running out of gas. The gas theorems say
that, under conditions, starvation by running out of gas is avoidable:
there is an amount of gas `g` such that, with `g` or more added to the
frame, it does not run out of gas.

- For a call whose calldata selects no function, this needs no condition
  on the larger-gas run.
  Otherwise it holds when, given the calls' outcomes in the larger-gas
  run, the source run of the selected function stays inside the storage
  regions `H` (below) for every gas filling, the larger-gas run's call
  trace is bounded, and, for every gas filling, that source run does not
  stop with one of the errors listed in
  [`gas_source_exempt`](#def-e2eGasSufficient-gas_source_exempt):
  a value transfer that would overflow the recipient's balance
  ([`unspecified_behaviour_exempt`](#def-e2eDefs-unspecified_behaviour_exempt)),
  a contract creation whose init code exceeds the EVM's size limit (no
  amount of gas helps there), or, in a static call, `UNREACHABLE` or a
  runtime error other than a missing gas reading. A failed `abi_decode` is
  not among them.
- For deployment, under the same three conditions on the larger-gas
  constructor run (with `deploy_gas_source_exempt` in place of
  `gas_source_exempt`), running out of gas with that much gas implies
  the runtime bytecode plus immutables exceeds the EVM's code-size limit.

<!-- dossier: thm-e2eGasSufficientTop-e2e_deploy_gas_sufficient -->

<!-- dossier: thm-e2eDeployed-vyper_call_gas_sufficient_deployed -->

## What the theorems do not cover

- **Contracts with several modules.** The theorems cover single-module
  contracts. A statement for module lists (imports and exports) is stated as
  a target; its proof is open, and it is not shown here.
- **Contracts the compiler definition refuses.** If `compile_vyper` returns
  nothing, the theorems say nothing.
- **The frontend and the Python compiler.** Vyper's parsing and semantic
  analysis are not verified, and neither is vyper-hol's translation of
  their annotated AST into `tops`: the theorems take `tops` as given,
  whatever produced it, and ask only that `check_contract` accept it and
  `compile_vyper` compile it (with the other hypotheses). They are about
  the HOL compiler definition, not the `vyper` executable.
- **Revert data and exact gas.** A revert is matched by a revert, but its
  data isn't compared (beyond the empty revert on unmatched calldata). Gas
  sufficiency says some amount of gas is enough; it gives no bound.
- **Calls into the contract's code from elsewhere.** Frames running the
  contract's code under another address (`DELEGATECALL` from a proxy, an
  EIP-7702 delegation) and creation frames started by another contract's
  `CREATE` are outside the theorems' entry hypotheses.

## Checking it yourself

All the proof scripts are public. From a checkout of
[vyper-hol](https://github.com/verifereum/vyper-hol) at the commit in the
page's header, with [holbuild](https://github.com/HOL-Theorem-Prover/holbuild):

```sh
holbuild check e2eDeployedTheory:e2e_deploy_correctness_deployed \
  e2eDeployedTheory:vyper_call_correct_deployed \
  e2eGasSufficientTopTheory:e2e_deploy_gas_sufficient \
  e2eDeployedTheory:vyper_call_gas_sufficient_deployed
```

This builds every theory the theorems depend on and reports each theorem
clean when it rests on no admitted step, oracle or extra axiom.

<!-- dossier: index -->
