# Call outcome bounds and trace frames

The source interpreter raises a runtime error when a call or create
needs an outcome and the oracle list is empty. Venom aborts on exhaustion.
The call correctness premise bounds the length of the EVM frame's
`call_trace` by `LENGTH (call_trace es) < 2 ** 64`. Each outcome supplied
to the source and Venom comes from that trace.

## Concrete deployment and call checkpoint

`lowering/e2eWitnessComputeScript.sml` evaluates the `p23_imm_uint256`
fixture's compilation and deployment, then constructs a call from the
committed deployment state. Its theorems establish a source result of
`IntV 42`, the corresponding EVM return bytes, and empty call and gas-reading traces.

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
