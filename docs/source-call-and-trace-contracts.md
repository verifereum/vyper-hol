# Source-call bounds and call-trace frames

The source-call bound and EVM frame results provide interfaces for reasoning
about external calls during a compiled execution. The source bound limits
outcome consumption; the frame results describe the origin of observed
request/outcome snapshots and how account properties pass between them.

## Source-call bounds

`lowering/sourceCallCountScript.sml` defines three entry runners:

- `fn_entry_run` performs entry setup, evaluates missing argument defaults,
  binds arguments, applies the nonreentrant lock and evaluates the body.
- `call_entry_run` selects an exported function and invokes that runner.
- `deploy_entry_run` initializes the constructor environment and invokes
  the same runner.

The runners take explicit outcome and gas-observation lists. Their results
expose the interpreter state, including its remaining outcomes and requests.
They do not by themselves establish ABI dispatch or compiler correctness.

`entry_calls_within n os run` takes at most `n` supplied outcomes and calls
`entry_calls_within_from` with the remaining budget. At budget zero, an
unavailable entry (`NONE`) satisfies the predicate; an available execution
must leave an outcome list other than `SOME []`. At a successor budget, the
predicate appends a probe outcome. If execution exhausts that extended list,
it appends a failed outcome to the original prefix and checks the smaller
budget recursively. Otherwise the bound holds at this step.

The probe differs from `empty_failed_outcome` in its account balances. The
definition uses the distinction to detect CREATE outcome-account validation
and select the request-specific failed outcome when required. It does not
assert that arbitrary supplied outcomes satisfy the callee contracts.

`source_calls_within` and `deploy_source_calls_within` specialize this shared
predicate to the call and deployment runners. The bound alone does not
establish that an entry exists or that its execution succeeds.

## Concrete deployment and call checkpoint

`lowering/e2eWitnessComputeScript.sml` evaluates the `p23_imm_uint256`
fixture's compilation and deployment, then constructs a call from the
committed deployment state. Its theorems establish a source result of
`IntV 42`, the corresponding EVM return bytes, empty call/GAS traces and
source-call bounds for both entries with arbitrary gas-observation lists.

These results cover this concrete checkpoint. They do not constitute the
general deploy-to-call lifecycle theorem or discharge its source
request-prefix and callee-outcome obligations.

## EVM trace provenance and account frames

The `callTrace*` theories under `venom/codegen/proofs/` establish provenance
for entries in a frame's `call_trace`:

- `call_trace_entry_origin` locates the request and outcome snapshots at an
  observable step at the initial frame's depth. The step either completes
  at that depth or pushes a child whose return produces the outcome.
- `run_call_reaches_root_msgParams` preserves root-frame message parameters
  at that depth, including when the initial context stack is a singleton.
- `call_trace_entry_provenance` combines those facts with the root account.

`entry_origin`, `pending_origin` and `observer_origin` are local predicates
used by the provenance proof.

`call_trace_account_transient_frame` transfers a predicate of one account
and its transient storage from an observed request snapshot to its outcome
snapshot. It requires closure under foreign-account changes, closure under
account changes preserving code and storage, and the theorem's explicit
re-entry rely for frames executing as that account. Those assumptions are
part of the interface; the theorem is not an unconditional preservation
claim for arbitrary predicates or reentrant calls.

`lowering/guardPushProjectionsScript.sml` supplies two further projections:
a static pushed frame cannot have `Code` output, and its saved deletion
list equals the current rollback deletion list. The complete
callee-outcomes producer is a separate result.
