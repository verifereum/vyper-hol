# Single-module hypotheses

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## source_typing_ok

The checker accepts the module. The account's constant and immutable cells are typed and hold the folded constants. The source machine and transaction are well typed.

## call_state_rel

The EVM starts in a fresh frame running the installed code, from source machine `am` and transaction `tx`.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.

## storage_ok

The regions in `H` fit and are pairwise identical or disjoint within each storage kind. They are clear of the transient lock slots, and the initial storage decodes on them.

## call_within

For every successful calldata dispatch and every filling of the source gas readings, the run's regions and locks are among those in `H`, its roots fit, and each callee-returned storage decodes on those regions.
