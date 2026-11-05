# SSA availability integration probe

## Checked outputs

`dftGasInvSSAProbeTheory` builds at the default tactic timeout.

- `inv_remaining_head_vars` handles the original-order head, including an empty crossed prefix, using the existing SSA bubble-head boundary.
- `inv_remaining_head_operands` extends this to all operands for nonterminators other than INVOKE and CODECOPY.
- `inv_ev_step_availability` proves domain growth and labels/current-block preservation for a successful oracle step. GAS is handled by its actual oracle update; INVOKE by actual successful bind_outputs and caller-state merge, without any callee reflection premise.
- `inv_remaining_ev_step` deletes any successfully executed nonterminator from the residual original-order list and preserves the existing invariant.
- `inv_entry_pseudo_initialized` derives the initial invariant from the entry-label equation, successful PHIs, and successful execution of the remaining pseudo prefix. It does not assume strict-dominator availability or the initial invariant.
- `inv_entry_residual_extension` composes that initialization, one actual oracle step, residual deletion, head readiness, call-context preservation, and crossing totality to manufacture an OK step for the earliest residual predecessor.

## Premise provenance and exact limitations

The entry label identifies the genuine function-entry block and supplies strict-dominator availability through `strict_dom_vars_defined_entry`. The theorem leaves the incoming state otherwise arbitrary; it is not a theorem constructing that state from `ev_context` or `ev_reachable`.

The syntactic pseudo/normal partition and instruction well-formedness are explicit hypotheses. These are structural inputs, not an assumed execution invariant. Labels required by normal instructions are explicitly assumed bound in the entry state. Successful `eval_phis` is an actual semantic premise. It is kept distinct from execution of non-PHI pseudos.

The original SSAProbe integration expresses the remaining pseudo prefix using list-semantics `FOLDR (dft_exec_cons fuel ctx) OK`. **The companion `dftGasInvPseudoPrefixTheory` closes this semantic gap:** `inv_pseudo_step` checks all pseudo opcodes and proves equality to ordinary steps at arbitrary fuel. `inv_pseudo_prefix_fold` converts an actual successful `inv_ev_prefix` over a pseudo segment to the corresponding fold; it does not assume a common fuel for the prefix. `inv_pseudo_prefix_drop` specializes this to the remaining pseudo segment after PHIs. Finally `inv_entry_oracle_residual_extension` replaces exactly the fold premise of the connected integration theorem with an actual oracle-prefix premise. No source-prefix existence is assumed, and no source reachability is concluded.

After initialization, the deleted instruction is backed by an actual successful `ev_step`. Nonstaticness is inherited from the initial state through the existing list-prefix and oracle-step call-context boundaries. The next residual instruction's shape and the no-must-order relation to a memory observation are explicit syntactic inputs. SSA readiness is derived, not assumed.

## Outstanding consumers

1. Constructing the entry incoming state from ev_context/ev_reachable, including structural producers for the pseudo partition and label bounds at the intended use site. The entry-label-identified oracle pseudo-prefix consumer is now checked, but does not construct that incoming state.
2. Strict-dominator propagation at arbitrary jump/block entry states, not just function entry.
3. Value agreement and oracle trace exchange across contexts. Domain membership alone does not establish equal operand values.
4. Finite returning-callee reflection. Successful INVOKE preservation here does not establish a corresponding successful call in another context.

These results do not prove the frozen lowered-memory theorem, its general observation-prefix bridge, or forwarding preservation. They should be reviewed as a bounded diagnostic, not certification of the parent simulation kernel.
