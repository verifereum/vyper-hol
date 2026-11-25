# Call gas sufficiency hypotheses

The reachable CREATE size bound for this route is `call_entry_reachable_create_size_ok`.

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
