Theory s1PrefixBoolChain
Ancestors
  s1PrefixBoolChainWrapperFromReached s1PrefixBoolChainActualEntry

Theorem bool_chain_expr_prefix_ok:
  !cx ann p n args.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ann (BoolChain p n) args))) /\
    (!s'' x t.
       type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
         "Builtin args" s'' = (INL x,t) /\
       BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
       code_slice_source (BoolChain p n) args = NONE ==>
       body_exprs_full_ok cx args) /\
    (!s'' x t.
       type_check (builtin_args_length_ok (BoolChain p n) (LENGTH args))
         "Builtin args" s'' = (INL x,t) /\
       BoolChain p n <> Len /\ BoolChain p n <> Env MsgGas /\
       code_slice_source (BoolChain p n) args = NONE ==>
       body_exprs_prefix_ok cx args) ==>
    body_expr_prefix_ok cx (Builtin ann (BoolChain p n) args)
Proof
  match_mp_tac bool_chain_wrapper_prefix_from_reached >>
  ACCEPT_TAC bool_chain_actual_entry_certificate
QED
