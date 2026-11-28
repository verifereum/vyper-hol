# Deployment hypotheses

The constructor result and the handoff use the same gas filling. After
successful source deployment at a surviving target, the next source machine
satisfies `deployed H`. This supplies installed code and gives source typing,
source deployment and `storage_ok H` for every well-typed transaction to the
deployed address.

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deploy_typing_ok

The checker accepts the module in deployment mode. The source machine and transaction are well typed.

## deploy_entry_rel

The EVM starts in a fresh creation frame at the target, with the deployment
bytecode and encoded constructor arguments. The frame matches the source
transaction and its post-transfer state. The entry state has bounded balances,
calldata and returndata. The initial creation frame's gas limit is less than
2⁶⁴. The target's persistent and transient storage are empty.

## horizon_ok

The persistent and transient regions in `H` fit in the 256-bit slot space.
Regions sharing a backend are pairwise identical or disjoint. The transient
regions are disjoint from the transient lock slots.

## deploy_within

For every gas filling, the constructor observations stay within `H`, with
roots fitting and each observed storage backend decoding on the fixed regions,
including traces that end in `INR`.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.
