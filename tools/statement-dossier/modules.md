# Module-list hypotheses

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper_mods

The compiler produces deployment bytecode and runtime bytecode for the modules and their export list.

## source_typing_ok_mods

The checker accepts the linked unit and its exports. The account's constant and immutable cells are typed and hold the folded constants. The source machine and transaction are well typed.

## call_state_rel_mods

The EVM starts in a fresh frame running the installed code, from source machine `am` and transaction `tx`. The source machine holds the modules and exports for the target, and there is a main module.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.

## storage_ok

The regions in `H` fit and are pairwise identical or disjoint within each storage kind. They are clear of the transient lock slots, and the initial storage decodes on them.

## call_within_mods

For every successful dispatch through the deployed interface and every filling of the source gas readings, the run's regions and locks are among those in `H`, its roots fit, and each callee-returned storage decodes on those regions.
