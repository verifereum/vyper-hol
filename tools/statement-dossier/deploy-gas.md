# Deploy gas sufficiency hypotheses

The reachable CREATE size bound for this route is `deploy_entry_reachable_create_size_ok`.
For each larger gas budget, the gas guarantee checks `deploy_within H` on that
run's call trace. Every source gas filling of the constructor must stay within
`H`.

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
calldata and returndata. The initial creation frame's gas limit, before adding
gas for the larger-budget runs, is less than 2⁶⁴. The target's persistent and
transient storage are empty.

## horizon_ok

The persistent and transient regions in `H` fit in the 256-bit slot space.
Regions sharing a backend are pairwise identical or disjoint. The transient
regions are disjoint from the transient lock slots.
