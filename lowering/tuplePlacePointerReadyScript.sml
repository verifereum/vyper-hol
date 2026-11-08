(* Probe the proposed semantic-purity adapter before using same-state geometry. *)
Theory tuplePlacePointerReady
Ancestors
  supportedTargets targetPlaceLive vyperPureExpr

Theorem tuple_place_supported_gas_index_not_semantic_pure:
  supported_target_pure tops
    (SubscriptTarget (NameTarget "a") (Builtin (BaseT (UintT 256)) (Env MsgGas) [])) /\
  ~EVERY pure_expr (target_indices
    (SubscriptTarget (NameTarget "a") (Builtin (BaseT (UintT 256)) (Env MsgGas) [])))
Proof
  EVAL_TAC
QED
