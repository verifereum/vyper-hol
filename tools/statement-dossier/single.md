# Single-module hypotheses

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deployed

Deployment establishes the installed code and the source-side typing and deployment
facts at the target. `call_preserves_deployed` shows when a call keeps those facts.

## call_tx_well_typed

The source transaction is well typed. This predicate does not read `tx.function_name`
or `tx.args`.

## call_entry_rel

The EVM starts in a fresh frame for this transaction, with the entry value transfer reflected in the state.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.

## storage_ok

The regions in `H` fit and are pairwise identical or disjoint within each storage
kind. They are clear of the transient lock slots, and the initial storage decodes on
them. This predicate does not read `tx.function_name` or `tx.args`.

## call_within

For every successful calldata dispatch and every filling of the source gas readings, the run's regions and locks are among those in `H`, its roots fit, and each callee-returned storage decodes on those regions.
