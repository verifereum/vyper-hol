# Call gas sufficiency hypotheses

The reachable CREATE size bound for this route is `call_entry_reachable_create_size_ok`.
For each larger gas budget, the gas guarantee checks `call_within H` on that
run's call trace. For every successful calldata dispatch and every source gas
filling, the call's storage observations must stay within `H`.

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deployed

Deployment establishes the installed code at the target. For every well-typed
transaction to that address, `deployed H` supplies source typing, source
deployment and `storage_ok H`. The starting storage decodes on the regions
in `H`, which fit and are pairwise identical or disjoint within each storage
kind. The transient regions are disjoint from the transient lock slots.

## call_tx_well_typed

The source transaction is well typed. This predicate does not read `tx.function_name`
or `tx.args`.

## call_entry_rel

The EVM starts in a fresh frame for this transaction, with the entry value transfer reflected in the state.
