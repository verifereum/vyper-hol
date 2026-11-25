# Deployment hypotheses

The constructor result and the handoff use the same gas filling. The handoff
establishes `deployed` after successful source deployment if the target is not
queued for deletion, and establishes `storage_ok H` on the next source machine
for later transactions targeting that address.

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deploy_typing_ok

The checker accepts the module in deployment and runtime mode. The source machine and transaction are well typed.

## deploy_entry_rel

The EVM starts in a fresh creation frame at the target, with the deployment
bytecode and encoded constructor arguments. The frame matches the source
transaction and its post-transfer state. The target's persistent and transient
storage are empty at constructor entry.

## regions_consistent

Every persistent and transient region in `H` fits in the 256-bit slot space,
and regions sharing a backend are pairwise identical or disjoint.

## storage_locks_separated

The transient (`T`) regions in `H` are disjoint from the transient lock slots.

## deploy_within

For every gas filling, the constructor observations stay within `H`, with
roots fitting and each observed storage backend decoding on the fixed regions,
including traces that end in `INR`.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.
