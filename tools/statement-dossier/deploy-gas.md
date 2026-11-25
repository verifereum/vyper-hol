# Deploy gas sufficiency hypotheses

The reachable CREATE size bound for this route is `deploy_entry_reachable_create_size_ok`.

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deploy_typing_ok

The checker accepts the module in deployment and runtime mode. The source machine and transaction are well typed.

## deploy_state_rel

The EVM starts in a fresh creation frame at the target, with the deployment bytecode and encoded constructor arguments. The frame matches the source transaction and its post-transfer state.
