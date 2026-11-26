# Call gas sufficiency hypotheses

The reachable CREATE size bound for this route is `call_entry_reachable_create_size_ok`.

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## source_typing_ok

The checker accepts the module. The account's constant and immutable cells are typed and hold the folded constants. The source machine and transaction are well typed.

## call_state_rel

The EVM starts in a fresh frame running the installed code, from source machine `am` and transaction `tx`.
