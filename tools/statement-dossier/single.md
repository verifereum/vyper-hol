# Single-module hypotheses

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deployed

Deployment establishes the installed code at the target. For every well-typed
transaction to that address, `deployed H` supplies source typing, source
deployment and `storage_ok H`. The regions in `H` fit, are pairwise identical
or disjoint within each storage kind and avoid the transient lock slots. The
starting storage decodes on those regions. The theorem gives back `deployed H`
in the next transaction world after a root call whose target survives.

## call_tx_well_typed

The source transaction is well typed. This predicate does not read `tx.function_name`
or `tx.args`.

## call_entry_rel

The EVM starts in a fresh frame for this transaction, with the entry value transfer reflected in the state.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.

## call_within

For every successful calldata dispatch and every filling of the source gas readings, the run's regions and locks are among those in `H`, its roots fit, and each callee-returned storage decodes on those regions.
