# Deployment hypotheses

The constructor result and the handoff use the same gas filling when its storage
condition holds. The handoff establishes `deployed` after successful source
deployment if the target is not queued for deletion.

## IN

The finalizer is one of the accepted finalizers.

## compile_vyper

The compiler produces deployment bytecode and runtime bytecode for the module.

## deploy_typing_ok

The checker accepts the module in deployment and runtime mode. The source machine and transaction are well typed.

## deploy_state_rel

The EVM starts in a fresh creation frame at the target, with the deployment bytecode and encoded constructor arguments. The frame matches the source transaction and its post-transfer state.

## LENGTH

The call trace has fewer than 2⁶⁴ entries.
